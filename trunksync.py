#!/usr/bin/env python

"""
Copyright (c) 2009-2010, Matthew Kennard
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the <organization> nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY Matthew Kennard ''AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL Matthew Kennard BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
"""

"""
How the sync works:

 - Request from iPhone a list of all notes and last modification date

   e.g.

   NoteTwo 1/9/9
   NoteThree 2/9/9
   NoteFour 3/9/9
   NoteSix 5/9/9

 - Request from local directory a list of all notes and last modification date

   e.g.

   NoteOne 1/9/9
   NoteTwo 1/9/9
   NoteFour 4/9/9
   NoteFive 5/9/9
   NoteSix 5/9/9

 - Retrieve list of all notes and last modification date that was generated at the end of the last sync

   NoteOne 1/9/9
   NoteTwo 1/9/9
   NoteThree 2/9/9
   NoteFour 3/9/9
   NoteSix 4/9/9

 - Work out what has changed locally and on the iPhone

   Should be:

   NoteOne *DELETED FROM IPHONE* -> delete locally
   NoteTwo *NO CHANGE* -> do nothing
   NoteThree *DELETED FROM LOCAL DIRECTORY* -> delete from iPhone
   NoteFour *UPDATED LOCALLY* -> send new version to iPhone
   NoteFive *NEW LOCALLY* -> send new version to iPhone
   NoteSix *CONFLICT AS MODIFIED LOCALLY AND ON IPHONE* -> Ask user which version they want to keep

 - for each note from iPhone:
     * mark as NEW ON IPHONE if,
       * not in last sync list
     * mark as UPDATED ON IPHONE if,
       * in last sync list AND last modification date > last sync list
 - for each note locally:
     * mark as NEW LOCALLY if,
       * not in last sync list
     * mark as UPDATED LOCALLY if,
       * in last sync list AND last modification date > last sync list
 - for each note in last sync list:
     * mark as DELETED ON IPHONE if,
       * not in iPhone list
     * mark as DELETED LOCALLY if,
       * not in local list
 - resolve conflicts where a note exists in more than one mark list (except can be in noth DELETE ON IPHONE and DELETED LOCALLY lists)
 - update according to lists (including trigger revision control actions)
 - save new last sync list
"""

import sys
import os
import re
import time
import calendar
import urllib
import unicodedata
import string
import select
import logging
from getpass import getpass

import pybonjour
import httplib2
# stu 100919 - need to fix my tk installation
import easygui

DEFAULT_TRUNKS = ['Fly.local', 'Fly.local.']

IGNORE_FILES = ['.lastsync', '.DS_Store', 'Notes & Settings', '.hgignore']
IGNORE_DIRS = ['Pdf', 'pdf', 'Html', 'html', '.hg']

VALID_FILENAME_CHARS = "-_.() %s%s" % (string.ascii_letters, string.digits)

logging.basicConfig(level=logging.DEBUG)

# This is the global settings object.
# XXX: Should probably make SyncSettings a singleton
# and use that
settings = None



class IphoneConnectError(Exception):
    """
    Raise if there is an issue connecting with Trunk Notes
    running on the iPhone
    """
    pass


class Note(object):

    def __init__(self, name, last_modified, local_path=None):
        """
        @param name: Name of the note - e.g. HomePage
        @param last_modified: Time the note was last modified
        @param local_path: Where the note resides on the local filesystem
        """
        self.name = name
        self.last_modified = last_modified
        if not local_path:
            local_path = unicodedata.normalize('NFKD', unicode(name)).encode('ASCII', 'ignore')
            local_path = ''.join(c for c in local_path if c in VALID_FILENAME_CHARS) + '.txt'
            assert os.path.exists(local_path), 'If local_path is provided it must exist'
        self.local_path = local_path
        self.contents = None       # note text content, utf8
        self.file_contents = None  # binary (str) content of image/sound
    
    def __cmp__(self, other_note):
        """
        Notes are the same if they have the same name.
        TrunkSync is case insensitive even though Trunk Notes is not
        """
        # XXX: this could lead to loss of data if two notes on
        # the iphone have titles differing only in case...?
        # perhaps should use the .1.txt type thing locally and
        # preserve case distinctions.
        return cmp(self.name.lower(), other_note.name.lower())

    def __repr__(self):
        return '%s (%s)' % (self.name, self.last_modified)

    def hydrate_from_iphone(self):
        """
        Get the note from the iPhone
        """
        logging.debug(u'Getting note from device: %s' % (self.name, ))
        self.contents = settings.iphone_request('get_note', {'title': self.name})
        if self.contents is None:
            return
        if self.name.startswith('File:'):
            filename = self.name[5:]
            if filename:
                # This note has a file component which we should get
                self.file_contents = settings.iphone_get_file(filename)

    ## stu 100912
    def backup_to_local(self):
        """
        Backup the note to the local storage
        """
        # Make sure that local_path is an absolute path
        if not self.local_path.startswith(settings.local_dir):
            self.local_path = os.path.join(settings.local_dir, self.local_path)
        # Add tilde indicating backup
        self.local_path = self.local_path + '~'
        logging.debug('Making back-up of note to local: %s' % (self.local_path, ))
        # - macosx manpage for mktime() respects timezone set with tzset()
        # - but result is UTC (aka GMT)
        # - the following composition explicitly performs conversion to local time
        #utime = time.mktime(time.localtime(calendar.timegm(self.last_modified)))
        ## stu 110125 # fixed again (did the TN time format change after 100909?)
        utime = calendar.timegm(self.last_modified)
        f = open(self.local_path, 'w')
        f.write(self.contents)
        f.close()
        # Update last modified time on file to this notes last accessed time
        self.update_time(utime)
        # Do not update related files
        # # ...
        # Now remove tilde from local path name
        self.local_path = self.local_path.rstrip('~')
    ##

    def save_to_local(self):
        """
        Save the note to the local storage
        """
        # Make sure that local_path is an absolute path
        if not self.local_path.startswith(settings.local_dir):
            self.local_path = os.path.join(settings.local_dir, self.local_path)
        logging.debug('Saving note to local: %s' % (self.local_path, ))
        with codecs.open(self.local_path, 'w', 'utf-8') as f:
            f.write(self.contents)
        # Update last modified time on file to this notes last accessed time
        utime = calendar.timegm(self.last_modified)
        ## stu 110125 # fixed again (did the TN time format change after 100909?)
        self.update_time(utime)
        # If there is a related file, then save that as well
        if self.file_contents:
            file_path = os.path.join(settings.local_files_dir, self.name[5:])
            with open(file_path, 'wb') as f:
                f.write(self.file_contents)

    def update_time(self, new_time):
        """
        Update the time of the local file to be the same as new_time

        @param new_time: Timestamp
        """
        assert self.local_path is not None, "local_path not established"
        os.utime(self.local_path, (new_time, new_time))

    def delete_local(self):
        """
        Delete the local file representing this note
        """
        # Make sure that local_path is an absolute path
        if not self.local_path.startswith(settings.local_dir):
            self.local_path = os.path.join(settings.local_dir, self.local_path)
        logging.debug('Deleting from local: %s, %s' % (self.name, self.local_path))
        try:
            os.remove(self.local_path)
            logging.debug('Removed: %s' % (self.local_path, ))
        except OSError:
            try:
                # Try removing without extension
                stripped_path = self.local_path.rsplit('.', 1)[0]
                logging.debug('Deleting from local: %s, %s' % (self.name, stripped_path))
                os.remove(stripped_path)
                logging.debug('Removed: %s' % (stripped_path, ))
            except:
                pass

    def hydrate_from_local(self):
        """
        Get the note from local
        """

        logging.debug(u'Getting note from local: %s, %s' % (self.name, self.local_path))
        with codecs.open(self.local_path, 'r', 'utf-8') as f:
            self.contents = f.read()
        # Update the timestamp in the metadata
        new_contents = []
        substituted_timestamp = False
        for line in self.contents.splitlines():
            if not substituted_timestamp and line.startswith('Timestamp: '):
                # Substitute this line with the actual timestamp
                line = 'Timestamp: %s' % (time.strftime('%Y-%m-%d %H:%M:%S +0000', self.last_modified), )
                substituted_timestamp = True
            new_contents.append(line + os.linesep)
        self.contents = u''.join(new_contents)

    def save_to_iphone(self):
        """
        Save the note to the iPhone
        """
        logging.debug('Saving to device: %s' % (self.name, ))
        filename = os.path.basename(self.local_path)
        new_contents = settings.iphone_request('update_note', {'contents': self.contents, 'filename': filename})
        # If this is a file, and the file exists locally then upload the file
        if self.name.startswith('File:'):
            filename = self.name[5:]
            file_path = os.path.join(settings.local_files_dir, filename)
            if os.path.exists(file_path):
                pass
                settings.iphone_upload_file(filename, file_path)
            else:
                logging.warn('File for entry does not exist: %s, %s' % (file_path, self.name))
        return new_contents

    def delete_on_iphone(self):
        """
        Delete the note from the iPhone
        """
        logging.debug('Removing from device: %s' % (self.name, ))
        settings.iphone_request('remove_note', {'title': self.name})


class SyncSettings(object):

    def __init__(self, local_dir, local_files_dir, iphone_ip, iphone_port, iphone_user, iphone_password):
        """
        @param local_dir: Local directory where note text files will be stored
        @param local_files_dir: Local directory where images, sound recordings will be stored
        @param iphone_ip: IP address of iPhone
        @param iphone_port: Port
        @param iphone_user: Username (if required)
        @param iphone_password: Corresponding username (plaintext)
        """
        self.local_dir = local_dir
        self.local_files_dir = local_files_dir
        self.iphone_ip = iphone_ip
        self.iphone_port = iphone_port
        self.iphone_user = iphone_user
        self.iphone_password = iphone_password
        self.http = None
        self.uri = None
       
    def setup_iphone_connection(self):
        """
        Setup the connection object with the username and password credentials
        """
        self.http = httplib2.Http()
        if self.iphone_user:
            self.http.add_credentials(self.iphone_user, self.iphone_password)
        self.uri = 'http://%s:%s' % (self.iphone_ip, self.iphone_port)

    def iphone_request(self, request_type, request_data={}):
        """
        Make a request to Trunk Notes on the iPhone

        @param request_type: Type of request, e.g. uuid
        @param request_data: Dictionary of key/value pair arguments for request

        @return: String returned from request (None if 404)
        """
        request_dict = {}
        request_dict.update({'submit': 'sync-%s' % (request_type, )})
        request_dict.update(request_data)
        headers = {'Content-type': 'application/x-www-form-urlencoded'}
        response, content = self.http.request(self.uri, 'POST', headers=headers, body=urllib.urlencode(request_dict))
        if response['status'] == '200':
            return content
        elif response['status'] == '404':
            return None
        else:
            raise IphoneConnectError, response

    def iphone_get_file(self, filename):
        """
        Try and get a file from the iPhone

        @param filename: Filename on the iPhone

        @return: File contents (None if doesn't exist)
        """
        response, content = self.http.request('%s/files/%s' % (self.uri, filename), 'GET')
        if response['status'] == '200':
            return content
        elif response['status'] == '404':
            return None
        else:
            raise IphoneConnectError, response

    def iphone_upload_file(self, filename, local_path):
        """
        Upload a local file to the iPhone files store

        @param filename: Filename
        @param local_path: Path to local file

        @return: Result of making request
        """
        # Read entire file into memory - not ideal...
        file_contents = open(local_path, 'r').read()
        boundary = '----------ThIs_Is_tHe_bouNdaRY_$'
        crlf = '\r\n'
        l = ['--' + boundary,
             'Content-disposition: form-data; filename="%s"' % (filename, ),
             'Content-type: application/octet-stream',
             '',
             file_contents,
             '--' + boundary + '--',
             '',
            ]
        body = crlf.join(l)
        headers = {'Content-type': 'multipart/form-data; boundary=%s' % (boundary, ),
                   'Content-length': str(len(body)),
                  }
        response, content = self.http.request(self.uri, 'POST', headers=headers, body=body)
        if response['status'] == '200':
            return content
        else:
            raise IphoneConnectError, response



class SyncAnalyser(object):
    
    def __init__(self, iphone_notes, local_notes, lastsync_notes, ui=None):
        """
        @param iphone_list: List of iPhone notes (note name and last modification date)
        @param local_list: List of local notes (note name and last modification date)
        @param lastsync_list: List of notes as they stood at the end of the last sync (note name and last modification date)
        @param ui: A reference to the UI being used, None if no UI
        """
        self.iphone_notes = iphone_notes
        self.local_notes = local_notes
        self.lastsync_notes = lastsync_notes
        self.ui = ui
        # List of notes marked as
        self.new_on_iphone = []
        self.updated_on_iphone = []
        self.new_locally = []
        self.updated_locally = []
        self.deleted_on_iphone = []
        self.deleted_locally = []
        ## stu 100912
        self.overridden_on_iphone = []
        self.overridden_locally = []
        ##
        
    def analyse(self):
        """
        >>> iphone_notes = [Note('NoteTwo', 1), Note('NoteThree', 2), Note('NoteFour', 3), Note('NoteSix', 5)]
        >>> local_notes = [Note('NoteOne', 1), Note('NoteTwo', 1), Note('NoteFour', 4), Note('NoteFive', 5), Note('NoteSix', 5)]
        >>> lastsync_notes = [Note('NoteOne', 1), Note('NoteTwo', 1), Note('NoteThree', 2), Note('NoteFour', 3), Note('NoteSix', 4)]
        >>> t = SyncAnalyser(iphone_notes, local_notes, lastsync_notes)
        >>> t.analyse()
        Resolve conflict: A note with the same name has been updated on both the iPhone and locally since last sync
        >>> print t.new_on_iphone
        []
        >>> print t.updated_on_iphone
        [NoteSix (5)]
        >>> print t.new_locally
        [NoteFive (5)]
        >>> print t.updated_locally
        [NoteFour (4), NoteSix (5)]
        >>> print t.deleted_on_iphone
        [NoteOne (1)]
        >>> print t.deleted_locally
        [NoteThree (2)]
        """
        try:
            # - for each note from iPhone:
            #  * mark as NEW ON IPHONE if,
            #    * not in last sync list
            #  * mark as UPDATE ON IPHONE if,
            #    * in last sync list AND last modification date > last sync list
            for note in self.iphone_notes:
                if not note in self.lastsync_notes:
                    self.new_on_iphone.append(note)
                else:
                    i = self.lastsync_notes.index(note)
                    if i >= 0 and note.last_modified > self.lastsync_notes[i].last_modified:
                        # Get the path of the note locally, so that when the local
                        # note is updated the correct file will be written to
                        i2 = self.local_notes.index(note)
                        assert i2 >= 0, 'Note mentioned in last sync but no connected local note'
                        note.local_path = self.local_notes[i2].local_path
                        self.updated_on_iphone.append(note)
            # - for each note locally:
            #     * mark as NEW LOCALLY if,
            #       * not in last sync list
            #     * mark as UPDATED LOCALLY if,
            #       * in last sync list AND last modification date > last sync list
            for note in self.local_notes:
                if not note in self.lastsync_notes:
                    self.new_locally.append(note)
                else:
                    i = self.lastsync_notes.index(note)
                    if i >=0 and note.last_modified > self.lastsync_notes[i].last_modified:
                        self.updated_locally.append(note)
            # - for each note in last sync list:
            #     * mark as DELETED ON IPHONE if,
            #       * not in iPhone list
            #     * mark as DELETED LOCALLY if,
            #       * not in local list
            for note in self.lastsync_notes:
                if not note in self.iphone_notes:
                    self.deleted_on_iphone.append(note)
                if not note in self.local_notes:
                    self.deleted_locally.append(note)
            # Resolve conflicts
            for note in self.new_on_iphone:
                if note in self.new_locally:
                    if self.ui:
                        ## stu 100912 - added backups, when conflicts discovered
                        answer = self.ui.resolve_conflict('%s has been created on your mobile device and locally.' % (note.name, ), ['device', 'local'])
                        if answer == 'device':
                            # User has chosen to keep one on device, so remove local note reference
                            self.overridden_locally.append(note)
                            self.new_locally.remove(note)
                        elif answer == 'local':
                            self.overridden_on_iphone.append(note)
                            self.new_on_iphone.remove(note)
                        else:
                            assert False, 'Invalid resolve choice'
                        ##
                        #answer = self.ui.resolve_conflict('%s has been created on your mobile device and locally.' % (note.name, ), ['device', 'local'])
                        #if answer == 'device':
                        #    # User has chosen to keep one on device, so remove local note reference
                        #    self.new_locally.remove(note)
                        #elif answer == 'local':
                        #    self.new_on_iphone.remove(note)
                        #else:
                        #    assert False, 'Invalid resolve choice'
                        ##
                    else:
                        print 'Resolve conflict: A note with the same name has been created on both the iPhone and locally since last sync'
                assert not note in self.updated_locally, 'Note new on iPhone but updated locally'
            for note in self.updated_on_iphone:
                if note in self.updated_locally:
                    if self.ui:
                        ## stu 100912 - logic to backup or diff, when conflicts discovered
                        answer = self.ui.resolve_conflict('%s has been updated on your mobile device and locally.' % (note.name, ), ['device', 'local'])
                        if answer == 'device':
                            # User has chosen to keep one on device, so remove local note reference
                            self.overridden_locally.append(note)
                            self.updated_locally.remove(note)
                        elif answer == 'local':
                            self.overridden_on_iphone.append(note)
                            self.updated_on_iphone.remove(note)
                        else:
                            assert False, 'Invalid resolve choice'
                        ##
                        #answer = self.ui.resolve_conflict('%s has been updated on your mobile device and locally.' % (note.name, ), ['device', 'local'])
                        #if answer == 'device':
                        #    # User has chosen to keep one on device, so remove local note reference
                        #    self.updated_locally.remove(note)
                        #elif answer == 'local':
                        #    self.updated_on_iphone.remove(note)
                        #else:
                        #    assert False, 'Invalid resolve choice'
                        ##
                    else:
                        print 'Resolve conflict: A note with the same name has been updated on both the iPhone and locally since last sync'
                assert not note in self.new_locally, 'Note updated on iPhone but new locally'
            # Make sure that no notes which were updated locally are scheduled for deletion locally
            for note in self.updated_locally:
                if note in self.deleted_on_iphone:
                    self.deleted_on_iphone.remove(note)
            # Make sure that no notes which were updated on the iphone are scheduled for deletion on the iphone
            for note in self.updated_on_iphone:
                if note in self.deleted_locally:
                    self.deleted_locally.remove(note)
        except ValueError, e:
            print note
            print e
            raise
        return True

    

class TrunkSync(object):

    def __init__(self, ui, trunk_ip, trunk_port, local_path, local_files_dir, last_sync_path, trunk_user=None, trunk_password=None):
        """
        @param ui: UI to use
        @param trunk_ip: IP address of running Trunk Notes on mobile device
        @param trunk_port
        @param local_path: Path to notes as text files on local computer
        @param local_files_dir: Path to directory containing images, sound recordings, etc
        @param last_sync_path: Path to file with last sync status
        @param trunk_user: username to use
        @param trunk_password: password
        """
        self.ui = ui
        self.trunk_ip = trunk_ip
        self.trunk_port = trunk_port
        self.local_path = local_path
        self.last_sync_path = last_sync_path
        self.settings = SyncSettings(local_path, local_files_dir, trunk_ip, trunk_port, trunk_user, trunk_password)
        self.settings.setup_iphone_connection()
        # Get the UUID of the device and modify last_sync_path accordingly
        # This is to support syncing with multiple devices
        uuid = self.settings.iphone_request('uuid')
        self.last_sync_path += '-%s' % (uuid, )

    def get_notes_from_iphone(self):
        """
        Get a list of notes form the iPhone

        @return: List of Note instances
        """
        raw_notes = settings.iphone_request('notes_list')
        notes = []
        for note in raw_notes.splitlines():
            note = note.strip()
            if note:
                timestamp, title = note.split(':', 1)
                notes.append(Note(title, time.gmtime(int(timestamp))))
        return notes

    def get_notes_from_local(self):
        """
        Get a list of notes from the local computer

        @return: List of Note instances
        """
        notes = []
        # For each file in the local directory
        for dirpath, dirnames, filenames in os.walk(settings.local_dir):
            ## stu 101121 - exclude directories
            skip_dir = False
            for dd in IGNORE_DIRS:
                if "/"+dd in dirpath:
                    skip_dir = True
                    break
            if skip_dir:
                continue
            ##
            for filename in filenames:
                ## stu 100912
                if filename.startswith('.') or filename.endswith('~') or filename in IGNORE_FILES:
                   continue
                #if filename.startswith('.') or filename in IGNORE_FILES:
                #    continue
                ##
                note_path = os.path.join(dirpath, filename)
                # For a local note the timestamp is just the file's last modified date
                last_modified = time.gmtime(os.stat(note_path).st_mtime)
                # TODO: Will above work on Windows - or does time need to be treated differently???
                # However its title is preferrably from the Title: metadata, if this does
                # not exist then it will be the filename (minus the file extension)
                f = open(note_path, 'r')
                note_name = None
                line = f.readline()
                while line:
                    if line.startswith('Title: '):
                        note_name = line.split(':', 1)[1].strip()
                        break
                    line = f.readline()
                f.close()
                if not note_name:
                    # Remove any file extension
                    note_name = filename.rsplit('.', 1)[0]
                notes.append(Note(note_name, last_modified, local_path=note_path))
        return notes

    def get_notes_from_lastsync(self):
        """
        Get a list of notes as they were the last time sync happened

        @return: List of Note instances
        """
        notes = []
        # Assuming not the first time synced with this directory
        if os.path.exists(self.last_sync_path):
            for line in open(self.last_sync_path, 'r').readlines():
                line = line.strip()
                if line:
                    timestamp, title = line.split(':', 1)
                notes.append(Note(title, time.gmtime(int(timestamp))))
        return notes

    def sync(self, mode='sync'):
        """
        Perform synchronization

        Can either, sync - a bi-directional synchronization of notes
                    backup - get notes from iPhone only, overwriting local modifications
                    restore - Send local files to iPhonen regardless of iPhone notes

        @param mode: Either sync, backup or restore
        """
        assert mode in ('sync', 'backup', 'restore')
        # Check that required directories exist - if they don't then create
        try:
            if not os.path.exists(settings.local_dir):
                os.makedirs(settings.local_dir)
            if not os.path.exists(settings.local_files_dir):
                os.makedirs(settings.local_files_dir)
        except Exception, e:
            self.ui.error('Could not create Trunk Sync directories')
            sys.exit(1)
        # Get lists of notes from the three sources
        iphone_notes = self.get_notes_from_iphone()
        local_notes = self.get_notes_from_local()
        lastsync_notes = self.get_notes_from_lastsync()
        # Tell the user that the sync is going to start
        if not self.ui.inform_sync_start():
            return False
        # Analyse the notes, and resolve conflicts (if synchronising)
        analyser = SyncAnalyser(iphone_notes, local_notes, lastsync_notes, self.ui)
        if mode != 'sync' or analyser.analyse():
            if mode == 'backup':
                # If backing up then new_on_iphone is all notes from the iPhone
                analyser.new_on_iphone = iphone_notes
            elif mode == 'restore':
                # If restoring then new_locally is all notes from the local store
                analyser.new_locally = local_notes
            ## stu 100912
            # Backup new_locally notes that have been overridden
            for note in analyser.overridden_locally:
                note.hydrate_from_local(settings)
                note.backup_to_local(settings)
            # Backup new_on_iphone notes that have been overridden
            for note in analyser.overridden_on_iphone:
                note.hydrate_from_iphone(settings)
                note.backup_to_local(settings)
            ##
            # Update local notes with notes from iPhone
            for note in analyser.new_on_iphone:
                note.hydrate_from_iphone(settings)
                note.save_to_local(settings)
            for note in analyser.updated_on_iphone:
                note.hydrate_from_iphone(settings)
                note.save_to_local(settings)
            for note in analyser.deleted_on_iphone:
                note.delete_local(settings)
            # Update iPhone notes with local changes
            for note in analyser.new_locally:
                note.hydrate_from_local(settings)
                new_contents = note.save_to_iphone(settings)
                if new_contents is None:
                    continue
                # Since this is a note which has been created locally
                # the note will now be retrieved from the mobile device
                # and saved back locally so the Trunk Notes header
                # is in place
                if not new_contents.startswith('ERROR'):
                    note.contents = new_contents
                    # Update the notes title
                    for line in note.contents.split('\n'):
                        if line.startswith('Title: '):
                            note_name = line.split(':', 1)[1].strip()
                            note.name = note_name
                            break
                    note.save_to_local(settings)
                else:
                    logging.error('Saving note to device returned ERROR')
            for note in analyser.updated_locally:
                note.hydrate_from_local(settings)
                note.save_to_iphone(settings)
            for note in analyser.deleted_locally:
                note.delete_on_iphone(settings)
            # Finally get a raw list of notes from the iPhone
            # and save this as the lastsync file
            raw_notes = settings.iphone_request('notes_list')
            with codecs.open(self.last_sync_path, 'w', 'utf-8') as last_sync_file:
                last_sync_file.write(raw_notes)
            # Update timestamps on those notes which were new locally
            # but were replaced with versions from the iPhone
            times_from_iphone = {}
            for line in raw_notes.split('\n'):
                if ':' in line:
                    timestamp, note_name = line.split(':', 1)
                    try:
                        times_from_iphone[note_name] = int(timestamp)
                    except ValueError:
                        logging.warn('Error in timestamp for note: %s' % (note_name, ))
            for note in analyser.new_locally:
                try:
                    timestamp = times_from_iphone.get(note.name)
                except:
                    timestamp = None
                if timestamp:
                    note.update_time(timestamp)
                else:
                    ## stu 2010-09-12
                    logging.warn('Could not update the local timestamp of '
                            'note: %s' % (note.name, ))
                    ##
                    #logging.warn('Could not update the timestamp of '
                    #             'note "%s" on device' % (note.name, ))
                    ##
        return True



class TrunkDeviceFinder(object):
    """
    Find a running Trunk Notes instance using Bonjour
    """

    timeout = 5

    def __init__(self):
        self.bonjour_clients = []

    def resolve_callback(self, sdRef, flags, interfaceIndex, errorCode, fullname,
                     hosttarget, port, txtRecord):
        if errorCode == pybonjour.kDNSServiceErr_NoError:
            # Only care about TrunkNotes service
            if fullname.startswith('TrunkNotes._http._tcp'):
                self.bonjour_clients.append((fullname, hosttarget, port))

    def bonjour_search(self):
        self.browse_sdRef = pybonjour.DNSServiceBrowse(regtype='_http._tcp.',
                                                       callBack=self.browse_callback)
        try:
            while not self.bonjour_clients:
                ready = select.select([self.browse_sdRef], [], [])
                if self.browse_sdRef in ready[0]:
                    pybonjour.DNSServiceProcessResult(self.browse_sdRef)
        finally:
            self.browse_sdRef.close()

    def browse_callback(self, sdRef, flags, interfaceIndex, errorCode, serviceName,
                    regtype, replyDomain):
        if errorCode != pybonjour.kDNSServiceErr_NoError:
            return

        if not (flags & pybonjour.kDNSServiceFlagsAdd):
            return

        resolve_sdRef = pybonjour.DNSServiceResolve(0,
                                                    interfaceIndex,
                                                    serviceName,
                                                    regtype,
                                                    replyDomain,
                                                    self.resolve_callback)

        try:
            while not self.bonjour_clients:
                ready = select.select([resolve_sdRef], [], [], self.timeout)
                if resolve_sdRef not in ready[0]:
                    break
                pybonjour.DNSServiceProcessResult(resolve_sdRef)
        finally:
            resolve_sdRef.close()



class TrunkSyncSimpleUi(object):

    def __init__(self):
        ## stu 100912
        self.local_path      = os.path.join(os.environ['HOME'], 'Documents', 'TrunkNotes', 'Notes'      ) 
        self.local_files_dir = os.path.join(os.environ['HOME'], 'Documents', 'TrunkNotes', 'Files'      ) 
        self.last_sync_path  = os.path.join(os.environ['HOME'], 'Documents', 'TrunkNotes', '.trunksync' ) 
        ##
        #self.local_path      = os.path.join(os.environ['HOME'], 'trunksync'      ) 
        #self.local_files_dir = os.path.join(os.environ['HOME'], 'trunksyncfiles' ) 
        #self.last_sync_path  = os.path.join(os.environ['HOME'], '.trunksync'     ) 
        ##
        self.username = None
        self.password = None

    def find_trunk(self):
        device_finder = TrunkDeviceFinder()
        device_finder.bonjour_search()
        return device_finder.bonjour_clients

    def inform_sync_start(self):
        print 'Trunk Sync starting'
        return True

    def error(self, message):
        print message

    def confirm_instance(self, instances):
        chosen_n = 0
        ## stu 100920
        n = 0
        assert len(instances) > 0, 'precondition of confirm_instance violated'
        for instance in instances:
            n += 1
            if (instance[1].strip() in DEFAULT_TRUNKS):
                chosen_n = n
                print 'Synching with Trunk instance: %d. %s' % (n, instance[1])
        ##
        while not (chosen_n > 0 and chosen_n <= len(instances)):
            print 'Choose Trunk to sync with:'
            n = 0
            for instance in instances:
                n += 1
                print '%s. %s' % (n, instance[1])
            chosen_n = raw_input('Choice: ')
            try:
                chosen_n = int(chosen_n)
            except ValueError:
                chosen_n = 0
        return instances[chosen_n - 1]

    def resolve_conflict(self, conflict_description, choices):
        chosen_n = 0
        while not (chosen_n > 0 and chosen_n <= len(choices)):
            print conflict_description
            n = 0
            for choice in choices:
                n += 1
                print '%s. %s' % (n, choice)
            chosen_n = raw_input('Choice: ')
            try:
                chosen_n = int(chosen_n)
            except ValueError:
                chosen_n = 0
        return choices[chosen_n - 1]
    
    def start(self):
        # 1. Find devices running Trunk and the port
        trunk_instances = self.find_trunk()
        # 2. Confirm with user which Trunk instance they want to use
        chosen_instance = self.confirm_instance(trunk_instances)
        # 3. Sync with this Trunk instances
        username = self.username
        password = self.password
        success = False
        while not success:
            try:
                sync = TrunkSync(self,
                                 chosen_instance[1],
                                 chosen_instance[2],
                                 self.local_path,
                                 self.local_files_dir,
                                 self.last_sync_path,
                                 trunk_user=username,
                                 trunk_password=password)
                success = sync.sync()
            except IphoneConnectError, e:
                if e[0]['status'] == '401':
                    # Authentication error - prompt user
                    username = raw_input('Username: ')
                    password = getpass('Password: ')
                else:
                    # Unknown error
                    raise



class TrunkSyncEasyUi(object):

    def __init__(self):
        self.local_path = None
        self.local_files_dir = None
        self.last_sync_path = None
        if sys.platform == 'darwin':
            base = os.path.join(os.environ['HOME'],
                                'Library',
                                'Application Support',
                                'trunksync',
                               )
            self.local_path = os.path.join(base, 'notes')
            self.local_files_dir = os.path.join(base, 'files')
            self.last_sync_path = os.path.join(base, 'sync')
	elif sys.platform == 'win32':
            base = os.path.join(os.environ['USERPROFILE'],
                                'trunksync',
                               )
            self.local_path = os.path.join(base, 'notes')
            self.local_files_dir = os.path.join(base, 'files')
            self.last_sync_path = os.path.join(base, 'sync')
        self.username = None
        self.password = None

    def find_trunk(self):
        device_finder = TrunkDeviceFinder()
        device_finder.bonjour_search()
        return device_finder.bonjour_clients

    def inform_sync_start(self):
        return easygui.ccbox('Starting synchronization with Trunk Notes. ' +
                             'You will be asked to resolve any conflicts before synchronization starts',
                             'Trunk Sync',
                            )

    def error(self, message):
        easygui.msgbox('Error: %s. Trunk Sync will now exit' % (message, ),
                       'Trunk Sync',
                      )

    def confirm_instance(self, instances):
        chosen_d = easygui.choicebox('Choose Trunk Notes to sync with:',
                                     'Trunk Sync',
                                     [instance[1] for instance in instances]
                                    )
        for instance in instances:
            if instance[1] == chosen_d:
                return instance
        return None

    def resolve_conflict(self, conflict_description, choices):
        chosen_d = easygui.choicebox(conflict_description,
                                     'Trunk Sync',
                                     choices,
                                    )
        return chosen_d
 
    def start(self):
        if not self.local_path:
            easygui.msgbox('This is an unsupported platform (%s). Feel free to modify this code to add support!' % (sys.platform, ),
                          )
            return
        easygui.msgbox('Make sure Trunk Notes is running on your iPhone/iPad/iPod Touch. ' +
                       'Put Trunk Notes into Wi-Fi Sharing Mode then click Continue. It can ' +
                       'take a while to find some devices, depending on your network',
                       'Trunk Sync',
                       'Continue',
                      )
        # 1. Find devices running Trunk and the port
        trunk_instances = self.find_trunk()
        # 2. Confirm with user which Trunk instance they want to use
        chosen_instance = self.confirm_instance(trunk_instances)
        if not chosen_instance:
            easygui.msgbox('You cancelled mobile device selection. Trunk Sync will now exit')
            sys.exit(1)
        # 3. Get user to choose whether to sync, backup or restore
        sync_mode = easygui.buttonbox('You can perform a bi-directional synchronization of notes, ' +
                                      'backup all notes from your mobile device or restore local notes to your device',
                                      'Trunk Sync',
                                      ('Sync', 'Backup', 'Restore'),
                                     ).lower()
        ok_to_continue = True
        if sync_mode == 'backup':
            ok_to_continue = easygui.boolbox('Any local notes which have been modified will be updated with the note from your device. ' +
                                             'Are you sure you wish to continue?',
                                             'Trunk Sync',
                                            )
        elif sync_mode == 'restore':
            ok_to_continue = easygui.boolbox('Any notes on your device which have been modified will be updated with the note from this ' +
                                             'computer. Are you sure you wish to continue?',
                                             'Trunk Sync',
                                            )
        if not ok_to_continue:
            return
        # 4. Sync with this Trunk instances
        username = self.username
        password = self.password
        success = False
        while not success:
            try:
                sync = TrunkSync(self,
                                 chosen_instance[1],
                                 chosen_instance[2],
                                 self.local_path,
                                 self.local_files_dir,
                                 self.last_sync_path,
                                 trunk_user=username,
                                 trunk_password=password)
                success = sync.sync(sync_mode)
                if success:
                    easygui.msgbox('Trunk Sync has finished',
                                   'Trunk Sync',
                                  )
            except IphoneConnectError, e:
                if e[0]['status'] == '401':
                    # Authentication error - prompt user
                    username = easygui.enterbox('Username',
                                                'Trunk Sync',
                                                '',
                                               )
                    password = easygui.passwordbox('Password',
                                                   'Trunk Sync',
                                                  )
                else:
                    # Unknown error
                    raise



def _test():
    import doctest
    doctest.testmod()

if __name__ == '__main__':
    if '-t' in sys.argv:
        _test()
    elif '-c' in sys.argv:
        t = TrunkSyncSimpleUi()
        t.start()
    else:
        t = TrunkSyncEasyUi()
        t.start()
