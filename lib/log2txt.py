#
# Copyright (c) 2015 Lutz Hofmann
# Licensed under the MIT license, see LICENSE.txt for details.
#
#
# This script converts log files as output by harmonic.m to text files
#

import re
import glob

# log files to be processed
FILE_GLOB = '../log/*.log'

def convertLog(filename):
    state = ''

    with open(filename) as infile:
        with open(filename+'.txt', 'w') as outfile:
            for line in infile:
                if state == 'CHAR':
                    outfile.write(line)
                    if line.startswith('Time'):
                        state = ''
                else:
                    if line.startswith('Time') or line.startswith('[*]') or line.startswith('Dim'):
                        outfile.write(line)
                    elif line.startswith('Characteristic polynomial'):
                        outfile.write(line)
                        state = 'CHAR'     

for filename in glob.glob(FILE_GLOB):
    print('Processing ' + filename)
    convertLog(filename)
