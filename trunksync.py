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

2011-01-23
UNICODE IN NOTES:
all text within the notes (including the titles) is stored in UTF-8 format, and
this is persisted across the computer(local) and device(remote) copies of the notes.
However the filenames used to store notes on the local computer are restricted
to ascii for portability purposes. Where multiple notes would map to a the same
filename, a number is added prior to the .txt extension to distinguish the files.
The note associated with a file should never be assumed purely from the filename,
but from the note title given in the first few lines of each local file note.

REQUIREMENTS:
WinXP / 2000:
  - install http://www.dns-sd.org/BonjourSDKSetup.zip
    (via http://www.dns-sd.org/ClientSetup.html)
Linux:
  - libdnssd. Ubuntu package is 'libavahi-compat-libdnssd1'
OS X:
  - no further requirements on OS x 10.6
  
NOTE:
It is important that your iOS device and local computer(s) are all time-synched
to a reasonable degree, otherwise repeated quick edit/syncs switching between
local/device for editing not keep the latest version accurately.
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
import codecs
import optparse
import shlex
import shutil
import textwrap
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

MODE_CHECK_PRESENT  = 40001
MODE_FIND_NOTE      = 40002
MODE_FIND_OR_CREATE = 40003
MODE_CREATE_NEW     = 40004

class IphoneConnectError(Exception):
    """
    Raise if there is an issue connecting with Trunk Notes
    running on the iPhone
    """
    pass

class SyncError(Exception):
    """
    Raise if there is an issue synchronising notes
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
        if local_path:
            if not local_path.startswith(settings.local_dir):
                local_path = os.path.join(settings.local_dir, local_path)
            assert os.path.exists(local_path), 'If local_path is provided it must exist'
        #if not local_path:
        #    local_path = unicodedata.normalize('NFKD', unicode(name)).encode('ASCII', 'ignore')
        #    local_path = ''.join(c for c in local_path if c in VALID_FILENAME_CHARS) + '.txt'
        #    # ? NOT TRUE FOR : File:fragment-length-bias.png
        #    # assert os.path.exists(local_path), 'If local_path is provided it must exist: ' + local_path
        self.local_path = local_path
        self.contents = None       # note text content, utf8
        self.file_contents = None  # binary (str) content of image/sound
    
    def _filename_base(self):
        """
        @return: proposed filename base, with no path info or extension.
        Note we currently return an ascii-compatible filename for portability
        reasons.
        Note file will always begin with the result of this function, but may
        then contain .[unique_id] - where unique_id is a decimal integer.
        """
        norm_path = unicodedata.normalize('NFKD', self.name)
        last_char_invalid = False
        target_fname = []
        for c in norm_path:
            if c in VALID_FILENAME_CHARS:
                target_fname.append(c)
                last_char_invalid = False
            else:
                if not last_char_invalid:
                    #invalid character replacement symbol: '_'
                    ##target_fname.append('_')
                    ###HERE
                    pass
                last_char_invalid = True
        return ''.join(target_fname)

    @staticmethod
    def get_internal_title(note_path):
        """
        @param note_path: full path to a note file
        @return: title of note form internal metadata, or None
        """
        note_name = None
        with codecs.open(note_path, 'r', 'utf-8') as f:
            for line in f:
                if line.startswith('Title: '):
                    note_name = line.split(':', 1)[1].strip()
                    break
        return note_name

    def establish_local_path(self, mode):
        # TODO: eliminate local_path entirely from the Note class
        # and create a pseudo filesystem which is based on note titles alone.
        # Could just take a decent hash (MD5/SHA1) of the note name and use
        # following
        #     # note_name -> filename
        #     from hashlib import sha1
        #     from base64 import b32encode
        #     from unicodedata import normalize
        #     note_norm = normalize('NFKD', note_name).encode('utf-8')
        #     filename = b32encode(sha1(note_norm)).digest())
        # which would be 32 chars long.
        # Given a file, the note is given by the 'title' meta-data.
        # (see get_internal_title fn above). Files without this would be
        # ignored.
        if mode == MODE_CHECK_PRESENT:
            assert self.local_path, "Expected note local file path to be set"
            assert os.path.isfile(self.local_path), "Expected note local file %s to exist"%(self.local_path)

        if self.local_path:
            # check file title matches the note (if it has a title - it could
            # be a newly created (by us) empty file)
            int_title = self.get_internal_title(self.local_path)
            assert int_title in [self.name, None], "%r:%r:%r"%(self.local_path, int_title, self.name)
            # don't care what we were asked for, once set local_path won't change.
            return

        # f_base is the full path plus initial note name (without any
        # id number or extension).
        f_base = os.path.join(settings.local_dir, self._filename_base())

        # find and return an existing file if we can
        if mode in [MODE_FIND_NOTE, MODE_FIND_OR_CREATE]:
            # see if a note matching f_base[.\d+]?.txt exists. If
            # such a note also contains the relevant title, select it.
            # If no such exists but a note of matching filename is
            # present, select that.
            candidate = None
            # want to use a regex match, but it gets very confused about
            # backslash characters in paths on windows, so convert to
            # forward slashes for comparison. they still work equally
            # well for the FS operations.
            fn_match_re = re.compile(r'%s(\.[0-9]+)?\.txt'%(f_base.replace('\\','/')))
            for fn in os.listdir(settings.local_dir):
                file_path = os.path.join(settings.local_dir, fn)
                if (fn_match_re.match(file_path.replace('\\','/')) and
                    os.path.isfile(file_path)):
                    note_internal_title = self.get_internal_title(file_path)
                    if note_internal_title == self.name:
                        # we have a winner - an authoritative match for note
                        candidate = file_path
                        break
                    elif note_internal_title:
                        # this note doesn't have any metadata, so not
                        # authoritative (don't break), but is a candidate.
                        # Any better (authoritative) match will override this.
                        candidate = file_path
            if candidate:
                self.local_path = candidate
                return

        if mode == MODE_FIND_NOTE:
            # we failed to find a matching note.
            # HERE
            print self
            raise SyncError(u"couldn't find requested note: %s" % (self.name, ))

        # at this point we are going to create a new file.
        if mode in [MODE_CREATE_NEW, MODE_FIND_OR_CREATE]:
            # Make sure that local_path is an absolute path
            target_fname = f_base
            idx = 0
            while True:
                # try to create f_base.txt, but if that exists
                # try f_base.1.txt, f_base.2.txt, and so on.
                candidate = u"%s%s.txt"%(target_fname, '' if not idx else '.%d'%idx)
                # XXX: we could probably do some locked open-for-writing type thing
                # to avoid the race-condition between os.path.exists and the file
                # creation.  Mustn't truncate existing files though.
                if not os.path.exists(candidate):
                    target_fname = candidate
                    # create the file, so it exists
                    with codecs.open(target_fname, 'w', 'utf-8') as f:
                        # create an empty note with this title. This
                        # will make this path the authoritative file
                        # for this note.
                        f.write("Title: %s\n"%(self.name))
                    break
                idx += 1
            self.local_path = target_fname
            return

        assert False, "Invalid mode given to establish_local_path"

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
        msg_local_path = "EMPTY"
        msg_contents = "0"
        msg_file_contents = "0"
        if self.local_path:
            msg_local_path = self.local_path
        if self.contents:
            msg_contents = "%d"%(len(self.contents))
        if self.file_contents:
            msg_file_contents = "%d"%(len(self.file_contents))
        return '%s - %s - %s - %s - %s' % (self.name, self.last_modified, msg_local_path, msg_contents, msg_file_contents)

    def hydrate_from_iphone(self):
        """
        Get the note from the iPhone
        """
        logging.debug(u'Getting note from device: %s' % (self.name, ))
        self.contents = settings.iphone_request('get_note', {'title': self.name.encode('utf-8')}).decode('utf-8')
        # HERE
        print self
        if self.contents is None:
            return
        filename = ''
        if self.name.startswith('File:'):
            filename = self.name[5:]
        #elif self.name.startswith('File'):
        #    filename = self.name[4:]
        if filename:
            try:
                # This note has a file component which we should get
                #self.file_contents = settings.iphone_get_file(filename)
                self.file_contents = settings.iphone_get_file(filename.encode('utf-8'))
            except e:
                logging.warn('Device file not found: %s' % (filename, ))
                print self
                print e
                raise


    def backup_to_local(self):
        """
        Backup the note to the local storage
        """
        # Add tilde indicating backup
        self.local_path = self.local_path + '~'
        self.establish_local_path(MODE_FIND_OR_CREATE)
        logging.debug('Making back-up of note to local: %s' % (self.local_path, ))
        with codecs.open(self.local_path, 'w', 'utf-8') as f:
            f.write(self.contents)
        # Update last modified time on file to this notes last accessed time
        utime = calendar.timegm(self.last_modified)
        ## stu 110125 # fixed again (did the TN time format change after 100909?)
        self.update_time(utime)
        # ... ignoring related images files ... 
        # Now remove tilde from local path name
        self.local_path = self.local_path.rstrip('~')

    def save_to_local(self):
        """
        Save the note to the local storage
        """
        self.establish_local_path(MODE_FIND_OR_CREATE)
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
        self.establish_local_path(MODE_FIND_NOTE)
        logging.debug(u'Deleting from local: %s, %s' % (self.name, self.local_path))
        try:
            os.remove(self.local_path)
            logging.debug(u'Removed: %s' % (self.local_path, ))
        except OSError:
            stripped_path,ext = os.path.splitext(self.local_path)
            if ext and os.path.isfile(stripped_path):
                # this did previously have an extension, i.e. we've
                # removed something, and a file exists without it.
                try:
                    # Try removing without extension
                    logging.debug(u'Deleting %s from local %s' % (self.name, stripped_path))
                    os.remove(stripped_path)
                    logging.debug(u'%s removed' % (stripped_path, ))
                except:
                    pass

    def hydrate_from_local(self):
        """
        Get the note from local
        """
        self.establish_local_path(MODE_FIND_NOTE)
        logging.debug(u'Getting note from local: %s, %s' % (self.name, self.local_path))
        with codecs.open(self.local_path, 'r', 'utf-8') as f:
            self.contents = f.read()
        # Update the timestamp in the metadata
        new_contents = []
        substituted_timestamp = False
        for line in self.contents.splitlines():
            if not substituted_timestamp and line.startswith('Timestamp: '):
                # Substitute this line with the actual timestamp
                line = u'Timestamp: %s' % (time.strftime('%Y-%m-%d %H:%M:%S +0000', self.last_modified), )
                substituted_timestamp = True
            new_contents.append(line + os.linesep)
        self.contents = u''.join(new_contents)

    def save_to_iphone(self):
        """
        Save the note to the iPhone
        """
        logging.debug(u'Saving to device: %s' % (self.name, ))
        self.establish_local_path(MODE_CHECK_PRESENT)
        filename = os.path.basename(self.local_path)
        # filename is only used if this is a new local file
        # which does not contain the Title: metadata. filename
        # is used to generate the note title.
        # any returned file contents must always be utf-8 unicode
        new_contents = settings.iphone_request('update_note', {'contents': self.contents.encode('utf-8'),
                                                               'filename': filename}).decode('utf-8')
        # If this is a file, and the file exists locally then upload the file
        filename = ''
        if self.name.startswith('File:'):
            filename = self.name[5:]
        #elif self.name.startswith('File'):
        #    filename = self.name[4:]
        if filename:
            file_path = os.path.join(settings.local_files_dir, filename)
            if os.path.exists(file_path):
                #settings.iphone_upload_file(filename, file_path)
                settings.iphone_upload_file(filename.encode('utf-8'), file_path)
            else:
                logging.warn(u'File for entry does not exist: %s, %s' % (file_path, self.name))
        return new_contents

    def delete_on_iphone(self):
        """
        Delete the note from the iPhone
        """
        logging.debug(u'Removing from device: %s' % (self.name, ))
        settings.iphone_request('remove_note', {'title': self.name.encode('utf-8')})


class SyncSettings(object):

    def __init__(self, options):
        """
        Establish SyncSettings object

        darwin:local_dir  [ ~/Documents/TrunkNotes/Notes      ] : Local directory where note text files will be stored
        other:local_dir   [ ~/trunksync                       ] : Local directory where note text files will be stored
        local_files_dir   [ ~/Documents/TrunkNotes/Files      ] : Local directory where images, sound recordings will be stored
        last_sync_path    [ ~/Documents/TrunkNotes/.trunksync ] : Local file where last-modifed timestamps will be stored
        iphone_user       [ None                              ] : Username (if required)  - see also options:credentials
        iphone_password   [ None                              ] : Corresponding username (plaintext)  - see also options:credentials
        quiet             [ options.quiet or False            ] : Verbosity
        iphone_ip         [ options.ipaddress                 ] : IP address of iPhone
        iphone_port       [ options.port                      ] : Port
        http              [ None                              ] : 
        uri               [ None                              ] : 
        sync_mode         [ options.sync_mode or 'default'    ] : 'sync', 'backup', 'restore', or 'wipelocal'
        """
        if sys.platform == 'darwin':
            base = os.environ['HOME']
        else:
            base = os.path.expanduser('~/trunksync')
        self.local_dir = os.path.join(base, 'Documents', 'TrunkNotes', 'Notes'      ) 
        self.local_files_dir = os.path.join(base, 'Documents', 'TrunkNotes', 'Files'      ) 
        self.last_sync_path = os.path.join(base, 'Documents', 'TrunkNotes', '.trunksync' ) 
        self.iphone_user = None
        self.iphone_password = None
        if options.credentials:
            with file(options.credentials) as f:
                creds = f.read()
            atoms = shlex.split(creds)
            if len(atoms) != 2:
                raise SystemExit("Invalid trunknotes credentials file")
            self.iphone_user, self.iphone_password = atoms

        self.quiet = options.quiet or False
        self.iphone_ip = options.ipaddress # will be None if not set
        self.iphone_port = options.port # will be None if not set
        self.http = None
        self.uri = None
        if options.sync_mode in ['sync', 'backup', 'restore', 'wipelocal']:
            self.sync_mode = options.sync_mode
        else:
            # XXX: note default is converted to sync automatically by SimpeUI,
            # but EasyUI asks user if not set.
            self.sync_mode = 'default'

    def setup_iphone_connection(self):
        """
        Setup the connection object with the username and password credentials
        """
        self.http = httplib2.Http()
        if self.iphone_user:
            self.http.add_credentials(self.iphone_user, self.iphone_password)
        self.uri = 'http://%s:%s' % (self.iphone_ip, self.iphone_port)
        # Get the UUID of the device and modify last_sync_path accordingly
        # This is to support syncing with multiple devices
        uuid = self.iphone_request('uuid')
        if not self.last_sync_path.endswith(uuid):
            self.last_sync_path += '-%s' % (uuid, )

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
        response, content = self.http.request(self.uri, 'POST',
                                              headers=headers, body=urllib.urlencode(request_dict))
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
        # file_contents = codecs.open(local_path, 'r', 'utf-8').read()
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
        ## stu 110131 - DISABLED, enable get_internal_title()
        #self.overridden_on_iphone = []
        #self.overridden_locally = []
        
    def analyse(self):
        """
        >>> iphone_notes = [Note('NoteTwo', 1), Note('NoteThree', 2), Note('NoteFour', 3), Note('NoteSix', 5)]
        >>> local_notes = [Note('NoteOne', 1), Note('NoteTwo', 1), Note('NoteFour', 4), Note('NoteFive', 5), Note('NoteSix', 5)]
        >>> lastsync_notes = [Note('NoteOne', 1), Note('NoteTwo', 1), Note('NoteThree', 2), Note('NoteFour', 3), Note('NoteSix', 4)]
        >>> t = SyncAnalyser(iphone_notes, local_notes, lastsync_notes)
        >>> t.analyse()
        Resolve conflict: A note with the same name has been updated on both the iPhone and locally since last sync
        True
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
        # - for each note from iPhone:
        #  * mark as NEW ON IPHONE if,
        #    * not in last sync list
        #  * mark as UPDATED ON IPHONE if,
        #    * in last sync list AND last modification date > last sync list
        for note in self.iphone_notes:
            if not note in self.lastsync_notes:
                # not seen this note before
                self.new_on_iphone.append(note)
            else:
                i = self.lastsync_notes.index(note)
                if note.last_modified > self.lastsync_notes[i].last_modified:
                    # # Get the path of the note locally, so that when the local
                    # # note is updated the correct file will be written to
                    # i2 = self.local_notes.index(note)
                    # assert i2 >= 0, 'Note mentioned in last sync but no connected local note'
                    # note.local_path = self.local_notes[i2].local_path
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
                if note.last_modified > self.lastsync_notes[i].last_modified:
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
        # Resolve conflicts.
        # Note it isn't possible for note to be 'new' on
        # one location and 'updated' on the other, as
        # 'new' status derives from a common source - the
        # last sync list.
        for note in self.new_on_iphone:
            if note in self.new_locally:
                if self.ui:
                    ## stu 100912 - added backups, when conflicts discovered
                    ## stu 110131 - DISABLED, enable get_internal_title()
                    noi, nol = self.new_on_iphone, self.new_locally
                    answer = self.ui.resolve_conflict('%s has been created on your mobile device and locally.' % (note.name, ), ['device', 'local'])
                    if answer == 'device':
                        # User has chosen to keep one on device, so remove local note reference
                        ## self.overridden_locally.append(note)
                        self.new_locally.remove(note)
                    elif answer == 'local':
                        ## self.overridden_on_iphone.append(note)
                        self.new_on_iphone.remove(note)
                    else:
                        assert False, 'Invalid resolve choice'
                else:
                    print 'Resolve conflict: A note with the same name has been created on both the iPhone and locally since last sync'
                    # XXX: perhaps 'return False' here?
            assert not note in self.updated_locally, 'Note new on iPhone but updated locally'
        for note in self.updated_on_iphone:
            if note in self.updated_locally:
                if self.ui:
                    ## stu 100912 - logic to backup or diff, when conflicts discovered
                    ## stu 110131 - DISABLED, enable get_internal_title()
                    answer = self.ui.resolve_conflict('%s has been updated on your mobile device and locally.' % (note.name, ), ['device', 'local'])
                    if answer == 'device':
                        # User has chosen to keep one on device, so remove local note reference
                        ##self.overridden_locally.append(note)
                        self.updated_locally.remove(note)
                    elif answer == 'local':
                        ##self.overridden_on_iphone.append(note)
                        self.updated_on_iphone.remove(note)
                    else:
                        assert False, 'Invalid resolve choice'
                else:
                    print 'Resolve conflict: A note with the same name has been updated on both the iPhone and locally since last sync'
                    # XXX: perhaps 'return False' here?
            assert not note in self.new_locally, 'Note updated on iPhone but new locally'
        # Make sure that no notes which were updated locally are scheduled for deletion locally
        for note in self.updated_locally:
            if note in self.deleted_on_iphone:
                self.deleted_on_iphone.remove(note)
        # Make sure that no notes which were updated on the iphone are scheduled for deletion on the iphone
        for note in self.updated_on_iphone:
            if note in self.deleted_locally:
                self.deleted_locally.remove(note)
        ### try:
        ### except ValueError, e:
        ###     print note
        ###     print e
        ###     raise
        return True

class TrunkSync(object):

    def __init__(self, ui):
        """
        @param ui: UI to use
        """

        self.ui = ui
        settings.setup_iphone_connection()

    def get_notes_from_iphone(self):
        """
        Get a list of notes form the iPhone

        @return: List of Note instances
        """
        raw_notes = settings.iphone_request('notes_list').decode('utf-8')
        notes = []
        for note in raw_notes.splitlines():
            note = note.strip()
            if note:
                timestamp, title = note.split(u':', 1)
                notes.append(Note(title, time.gmtime(int(timestamp))))
                # DEBUG HERE
                print timestamp + " - " + title
        return notes

    def get_notes_from_local(self):
        """
        Get a list of notes from the local computer

        @return: List of Note instances
        Only consider .txt files
        Exclude dot files
        Exclude backup (~ tilde) files
        Exclude IGNORE files
        """
        notes = {}
        # For each file in the local directory
        for dirpath, dirnames, filenames in os.walk(settings.local_dir):
            # stu 101121 - exclude directories
            skip_dir = False
            for dd in IGNORE_DIRS:
                if "/"+dd in dirpath:
                    skip_dir = True
                    break
            if skip_dir:
                continue
            for filename in filenames:
                if filename.startswith('.') or not filename.endswith('.txt') or filename.endswith('~') or filename in IGNORE_FILES:
                    continue
                    # only consider .txt files
                note_path = os.path.join(dirpath, filename)
                # For a local note the timestamp is just the files last modified date
                last_modified = time.gmtime(os.stat(note_path).st_mtime)
                # Note title is preferrably from the Title: metadata, if this does
                # not exist then it will be the filename (minus the file extension)
                note_name = Note.get_internal_title(note_path)
                if not note_name:
                    # Remove any file extension. Hopefully we don't have
                    # any other notes of the same name, but all bets are
                    # off really without the metadata.
                    note_name = os.path.splitext(filename)[0]
                if note_name in notes:
                    if notes[note_name].last_modified > last_modified:
                        logging.warn(u'Multiple local notes for "%s" - using most recent'%(note_name))
                        continue
                notes[note_name] = Note(note_name, last_modified, local_path=note_path)
        return notes.values()

    def get_notes_from_lastsync(self):
        """
        Get a list of notes as they were the last time sync happened

        @return: List of Note instances
        """
        notes = []
        # Assuming not the first time synced with this directory
        if os.path.exists(settings.last_sync_path):
            for line in codecs.open(settings.last_sync_path, 'r', 'utf-8').readlines():
                line = line.strip()
                if line:
                    timestamp, title = line.split(':', 1)
                notes.append(Note(title, time.gmtime(int(timestamp))))
        return notes

    def sync(self):
        """
        Perform synchronization

        Can either, sync - a bi-directional synchronization of notes
                    backup - get notes from iPhone only, overwriting local modifications
                    restore - Send local files to iPhonen regardless of iPhone notes

        uses settings.sync_mode: Either sync, backup or restore
        """
        mode = settings.sync_mode
        assert mode in ('sync', 'backup', 'restore', 'wipelocal')
        if mode == 'wipelocal':
            # remove last_sync file first, as if we're interrupted and
            # have removed notes/files but not updated sync file, corresponding
            # notes will get removed from the device. which is bad.
            try:
                os.remove(settings.last_sync_path)
            except OSError:
                pass
            try:
                shutil.rmtree(settings.local_dir)
            except OSError:
                pass
            try:
                shutil.rmtree(settings.local_files_dir)
            except OSError:
                pass
            return True

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
            # stu 100912
            ## stu 110131 - DISABLED, enable get_internal_title()
            # Backup new_locally notes that have been overridden
            ## for note in analyser.overridden_locally:
            ##     note.hydrate_from_local()
            ##     note.backup_to_local()
            # Backup new_on_iphone notes that have been overridden
            ## for note in analyser.overridden_on_iphone:
            ##     note.hydrate_from_iphone()
            #     note.backup_to_local()
            # Update local notes with notes from iPhone
            for note in analyser.new_on_iphone:
                note.hydrate_from_iphone()
                note.save_to_local()
            for note in analyser.updated_on_iphone:
                note.hydrate_from_iphone()
                note.save_to_local()
            for note in analyser.deleted_on_iphone:
                note.delete_local()
            # Update iPhone notes with local changes
            for note in analyser.new_locally:
                note.hydrate_from_local()
                new_contents = note.save_to_iphone()
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
                    note.save_to_local()
                else:
                    logging.error('Saving note to device returned ERROR')
            for note in analyser.updated_locally:
                note.hydrate_from_local()
                note.save_to_iphone()
            for note in analyser.deleted_locally:
                note.delete_on_iphone()
            # Finally get a raw list of notes from the iPhone
            # and save this as the lastsync file.
            #
            # Note we decode as utf-8 then re-encode in utf-8.
            # Alternatively we could just ensure we write
            # last_sync_file as binary, but that seems fragile.
            raw_notes = settings.iphone_request('notes_list').decode('utf-8')
            with codecs.open(settings.last_sync_path, 'w', 'utf-8') as last_sync_file:
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
                    logging.warn('Could not update the local timestamp of '
                                 'note: %s' % (note.name, ))


        self.ui.message('Trunk Sync has finished')
        return True



class TrunkDeviceFinder(object):
    """
    Find a running Trunk Notes instance using Bonjour
    """

    timeout = 5

    def __init__(self, ipaddr=None):
        self.bonjour_clients = []
        self.target_ip = ipaddr

    def resolve_callback(self, sdRef, flags, interfaceIndex, errorCode, fullname,
                     hosttarget, port, txtRecord):
        if errorCode == pybonjour.kDNSServiceErr_NoError:
            # Only care about TrunkNotes service
            # XXX: currently no unique id per device, so will only find one
            # device on the local network. If/when Trunk Notes app gets updated
            # to fix this, this will need updating too.
            if fullname.startswith('TrunkNotes._http._tcp'):
                if self.target_ip in [None, hosttarget]:
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


class TrunkSyncBaseUi(object):
    """Base class for SimpleUi and EasyUi"""

    def find_trunk(self):
        device_finder = TrunkDeviceFinder()
        device_finder.bonjour_search()
        return device_finder.bonjour_clients

    def get_trunk_instance(self):
        set_ip, set_port = settings.iphone_ip, settings.iphone_port
        if set_ip and set_port:
            chosen_instance = (None, set_ip, set_port)
        else:
            trunk_instances = self.find_trunk()
            if set_ip:
                # there should only be one trunk instance on any given IP
                chosen_instance = filter(lambda inst: inst[1] == set_ip,
                       trunk_instances)[0]
            else:
                # Confirm with user which Trunk instance they want to use
                chosen_instance = self.confirm_instance(trunk_instances)

        return chosen_instance

    def start(self):
        if not settings.quiet:
            self.wait_for_continue('Make sure Trunk Notes is running on your iPhone/iPad/iPod Touch. ' +
                                   'Put Trunk Notes into Wi-Fi Sharing Mode then click Continue. It can ' +
                                   'take a while to find some devices, depending on your network')

        # 1. Find devices running Trunk and the port
        chosen_instance = self.get_trunk_instance()
        if not chosen_instance:
            self.message('You cancelled mobile device selection. Trunk Sync will now exit')
            sys.exit(1)
        if not self.confirm_sync_mode():
            self.message('Operation cancelled.')
            sys.exit(1)
        settings.iphone_ip = chosen_instance[1]
        settings.iphone_port = chosen_instance[2]
        # 2. Sync with this Trunk instances
        success = False
        while not success:
            try:
                sync = TrunkSync(self)
                success = sync.sync()
            except IphoneConnectError, e:
                if e[0]['status'] == '401':
                    # Authentication error - prompt user
                    self.message('Authentication required')
                    settings.iphone_user = self.get_username()
                    settings.iphone_password = self.get_password()
                else:
                    # Unknown error
                    raise

class TrunkSyncSimpleUi(TrunkSyncBaseUi):
    """command line interface to trunksync"""


    def inform_sync_start(self):
        print 'Trunk Sync starting'
        return True

    def wait_for_continue(self, msg):
        self.message(msg)
        raw_input('Press [enter] to continue ')

    def message(self, msg):
        print os.linesep.join(textwrap.wrap(msg))

    def error(self, msg):
        # no different to normal message for SimpleUI
        self.message(msg)

    def confirm_sync_mode(self):
        """
        GUI mode asks user here if not explicitly set,
        but if using CLI then user can be expected to
        provide this in command line options
        """
        ok_to_continue = True
        if settings.sync_mode == 'default':
            settings.sync_mode = 'sync'
        elif settings.sync_mode == 'wipelocal':
            x = raw_input("""CAUTION.
            This will wipe all local trunksync data from this machine.
            You should probably use Trunk Notes' backup feature prior
            to this action to email yourself your data.
            Are you sure? (type 'yes' to continue with this action)
            """)
            ok_to_continue = (x == 'yes')
        return ok_to_continue

    def confirm_instance(self, instances):
        chosen_n = 0
        ## stu 110201 - ## stu 110127 - switching to beta2 solution ## stu 100920 -
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

    def get_username(self):
        return raw_input('Username: ')

    def get_password(self):
        return getpass('Password: ')


class TrunkSyncEasyUi(TrunkSyncBaseUi):
    """EasyGui interface to trunksync"""

    def inform_sync_start(self):
        return easygui.ccbox('Starting synchronization with Trunk Notes. ' +
                             'You will be asked to resolve any conflicts before synchronization starts',
                             'Trunk Sync',
                            )

    def message(self, msg):
        easygui.msgbox(msg,
                       'Trunk Sync',
                      )

    def wait_for_continue(self, msg):
        easygui.msgbox(msg,
                       'Trunk Sync',
                       'Continue'
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

    def confirm_sync_mode(self):
        ok_to_continue = True
        if settings.sync_mode == 'default':
            # Get user to choose whether to sync, backup or restore
            settings.sync_mode = easygui.buttonbox('You can perform a bi-directional synchronization of notes, ' +
                                          'backup all notes from your mobile device, restore local notes to your device, '+
                                          'or wipe all local Trunk Sync data from this machine',
                                          'Trunk Sync',
                                          ('Sync', 'Backup', 'Restore', 'Wipe Local'),
                                         ).lower().replace(' ','')
        if settings.sync_mode == 'backup' and not settings.quiet:
            ok_to_continue = easygui.boolbox('Any local notes which have been modified will be updated with the note from your device. ' +
                                             'Are you sure you wish to continue?',
                                             'Trunk Sync',
                                            )
        elif settings.sync_mode == 'restore' and not settings.quiet:
            ok_to_continue = easygui.boolbox('Any notes on your device which have been modified will be updated with the note from this ' +
                                             'computer. Are you sure you wish to continue?',
                                             'Trunk Sync',
                                            )
        elif settings.sync_mode == 'wipelocal':
            # warn user here regardless of settings.quiet
            ok_to_continue = easygui.boolbox('CAUTION: This will wipe all local trunksync data from this machine. You should probably use ' +
                                             'Trunk Notes backup feature prior to this action to email yourself your data. ' +
                                             'Are you sure you wish to continue?',
                                             'Trunk Sync'
                                            )
        return ok_to_continue

    def get_username(self):
        return easygui.enterbox('Username',
                                'Trunk Sync',
                                '',
                               )

    def get_password(self):
        return easygui.passwordbox('Password',
                                   'Trunk Sync',
                                  )

def _test():
    import doctest
    doctest.testmod()

def main(args=None):
    global settings
    parser = optparse.OptionParser()
    parser.add_option("-t", "--test", dest="test", action="store_true",
        help=optparse.SUPPRESS_HELP)
    parser.add_option("-c", "--cli", dest="cli", action="store_true",
        help="Use command line interface")
    parser.add_option("-q", "--quiet", dest="quiet", action="store_true",
        help="Quiet - don't bother user with unnecessary interaction")
    parser.add_option("-i", "--ip", dest="ipaddress", metavar="IP_ADDRESS",
        help="Specify iOS device IP address (optional: use bonjour if not specified)")
    parser.add_option("-p", "--port", dest="port", metavar="IP_PORT",
        type=int, default=10000,
        help="Specify Trunk Notes WiFi sharing port (optional: use bonjour if not specified)")
    parser.add_option("-r", "--credfile", dest="credentials", metavar="FILE",
        help="path of credentials file, containing username and password")
    parser.add_option("-m", "--mode", dest="sync_mode", choices=['sync', 'backup', 'restore', 'wipelocal'],
        help="sync mode, one of 'sync' [default], 'backup' (copy device->local), 'restore' (copy local->device), 'wipelocal' (remove all local sync info and data [CAUTION!])")
    if args is None:
        args = sys.argv[1:]

    options, args = parser.parse_args(args)
    if options.test:
        _test()
        sys.exit()
    else:
        settings = SyncSettings(options)
        if options.cli:
            t = TrunkSyncSimpleUi()
        else:
            t = TrunkSyncEasyUi()
        t.start()

if __name__ == '__main__':
    main()
