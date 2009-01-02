import os
from t import LIB9, CC, DEFINES, ROOT, INCLUDES, LIBS

OUT="ndate.exe"


INCLUDES+=r"""
libmp\port
"""

FNAMES=LIB9
FNAMES+=r"""
utils\ndate\ndate.c

lib9\exits.c
"""

FNAMES = ' '.join( (os.path.join(ROOT,x) for x in FNAMES.split()) )
INCLUDES = ' '.join( (('-I'+os.path.join(ROOT,x)) for x in INCLUDES.split()) )
LIBS = ' '.join( (('-l'+x) for x in LIBS.split()) )

cmd=r'%s -o %s %s %s %s %s' % (CC, OUT, DEFINES, INCLUDES, LIBS, FNAMES)
print cmd

os.system(cmd)
