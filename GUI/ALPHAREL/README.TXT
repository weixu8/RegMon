
Regmon for Windows NT/9x
Copyright (C) 1996-1999 Mark Russinovich and Bryce Cogswell
http://www.sysinternals.com

Using Regmon
------------

Start Regmon.exe from its home directory. Complete usage 
instructions are available in the on-line help file.

Building Regmon
----------------

Regmon consists of a device driver and a GUI. The NT driver was built with
the Windows NT DDK Build environment and the GUI was compiled with 
Microsoft Visual C++ 6.0. The VxD was built using Vireo Software's
(now NuMega Labs) VtoolsD 2.0. 

The help was entered with Microsoft Word 97 and Help Workshop 
for Word 97.

To install, copy Regmon.exe, Regvxd.vxd and regsys.sys to the same 
directory.

Terms of Use
------------

This software is provided "as is", without any guarantee made
as to its suitability or fitness for any particular use. It may
contain bugs, so use of this tool is at your own risk. We take
no responsilbity for any damage that may unintentionally be caused
through its use.

You may use the source in commercial applications without fee, however
any software distributed based on Regmon must have significant added
value in functionality over what is present here. For example, you 
cannot distribute or sell a Registry monitor based on this code, though
you can distribute and sell a product that uses Registry monitoring
to capture changes made during a software installation in order 
to perform an automatic uninstall.

You may not distribute Regmon in any form without express written
permission of Mark Russinovich or Bryce Cogswell.

Reporting Problems
------------------

If you encounter problems, please visit http://www.sysinternals.com
and download the latest version to see if the issue has been resolved.
If not, please send a bug report to:

	mark@sysinternals.com and cogswell@winternals.com
