
## Introduction



The trunksync program is a utility for the TrunkNotes app which synchronizes notes between an iOS device and a computer.  The original code was provided by Matthew Kennard from [AppsOnTheMove](http://appsonthemove.com/trunk/trunk-sync-beta), and was released under a BSD Open Source licence. 

This modified version of the program includes a number of enhancements to make it easier to sync notes and images between a desktop and your iOS device.  

## Terminology

local 
: the computer

device
: iOS system running Trunk Notes

## Changes

<span style="color:#F00;background-color:#555;font-weight:bold">TODO</span>: Condense and provide usage instructions

Here is a rough list of changes that were made to the trunksync.


 1. Automatically select an iOS device that matches one of the names specified in the variable DEFAULT_TRUNKS.
 1. When generating the list of local files to transfer to/from the device, ignore all files from the list IGNORE_FILES
 1. When generating the list of local files to transfer to/from the device, do not descend into directories from the list IGNORE_DIRS
 1. When generating the list of local image files to transfer to/from the device, only use extensions from the list IMAGE_EXTENSIONS
 1. When constructing the local filename for a note created on the device, simply remove invalid characters, rather than replace them with underscores "_"
 1. When the local file corresponding to a note can not be found, print debugging information about the note.
 1. For debugging purposes, included additional information in the compact representation of a note.  New fields include: local path, length of contents, and length of associated image contents
 1. Modified logging output for easier scanning
 1. Whenever contents of a note are retrieved from the device, print the compact note representation
 1. If an error is encountered when transferring images from the device to the computer, debugging information is printed
 1. (DISABLED) When a conflict is discovered, a backup of the overridden note is saved to the computer with a tilde extension
 1. (NEEDS IMPROVEMENT) Updated the calculation of the last modified time to better handle time zones.  This affects the local file's properties, which must be correct for proper synching.  The metadata field for the note can not be easily updated, because it is generated by the Trunk Notes app.
 1. Before uploading an image to the device, UTF8 encoding is applied to the image's filename
 1. Added documentation of options and defaults for the SyncSettings object
 1. Changed the base directory to point to the user's home directory, rather than '~/Library/Application Support/trunksync'
 1. Hardcoded local paths for notes (local_dir), images (local_files_dir), and the timestamp file (last_sync_path)
 1. Bugfix: When reading images, do not assume that binary image files are UTF8 encoded.  UTF8 encoding is for unicode characters.
 1. Added the ability to detect and upload new images that are located in the designated image folder
 1. (DISABLED) When a conflict is discovered, detect which files will be overwritten after user decides
 1. (NO LONGER NECESSARY) Error checking 
 1. Detect which notes corresponding to files in the designated image directory are new locally, or updated locally
 1. Added logging of notes list retrieved from the device
 1. Added code to ignore files from IGNORE_FILES and IGNORE_DIRS
 1. Added code to scan designated folder on the computer for images, and create corresponding notes for transfer to the device
 1. Added code to automatically select an instance of Trunk Notes that is discovered over the network (wifi, ...) and matches one of the names specified in DEFAULT_TRUNKS


