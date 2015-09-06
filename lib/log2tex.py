#
# Copyright (c) 2015 Lutz Hofmann
# Licensed under the MIT license, see LICENSE.txt for details.
#
#
# This script converts log files as output by harmonic.m to LaTeX files
# Needs to be run inside ./lib
#

import subprocess
import re
import glob

# log files to be processed
FILE_GLOB = '../log/*.log'
# path to magma executable (give full path if your envoironment is not set up properly)
MAGMA_EXEC = 'magma'



TEX_TABLE_HEADER = '''\\begin{{tabular}}{{| l | l |}}
\\multicolumn{{2}}{{l}}{{\\bf Heckeoperatoren der Form $\\diag({0})$}} \\\\
\\hline
$P$ & $\\chi^\\text{{char}}(T)$ \\\\
\\hline
'''

def convertLog(infile):
    state = k = P = char = ''
    data = []
    with open(infile) as f:
        for line in f:
            if state == 'CHAR':
                if line.startswith('Time'):
                    data.append( (int(k), P, char.strip()) )
                    state = k = P = char = ''
                else:
                    char += line
            elif state == 'HECKE':
                if line.startswith('Characteristic polynomial'):
                    char = line.split(': ')[1]
                    state = 'CHAR'
            else:
                if line.startswith('[*] Computing Hecke'):
                    hecke = re.search('k = (\d+), P = (.*)\.', line)
                    k = hecke.group(1)
                    P = hecke.group(2)
                    state = 'HECKE'

    with open(infile+'.tmp', 'w') as f:
        f.write('Attach("buildingLib.m");\n')
        f.write('Attach("latex.m");\n')
        f.write('import "latex.m" : LatexFactorization;\n')
        f.write('R<T> := PolynomialRing(Integers());\n')
        f.write('poly := [\n')
        for i,(k,P,char) in enumerate(data):
            f.write(char)
            if i < len(data)-1:
                f.write(',\n')
        f.write('];\n')
        f.write("""print "|||";
                   for p in poly do
                       print LatexFactorization(p);
                       print "|||";
                   end for;
                   exit;""")

    magma = subprocess.Popen([MAGMA_EXEC, infile+'.tmp'], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = magma.communicate()
    latex = out.split('|||')

    for i,(k,P,char) in enumerate(data):
        data[i] = (k,P,char,latex[i+1].strip())

    ks = frozenset(d[0] for d in data)

    with open(infile+'.tex', 'w') as f:
        for k in ks:
            if k == 1:
                f.write(TEX_TABLE_HEADER.format('1,1,P'))
            else:
                f.write(TEX_TABLE_HEADER.format('1,P,P'))
            for (_,P,_,charTex) in filter(lambda d: d[0] == k, data):
                f.write('$' + P + '$ &\n')
                tex = charTex.splitlines()
                for i in range(len(tex)-1):
                    tex[i] += '\\\\&'
                tex = '\n'.join(tex)
                f.write('$\\!\\begin{aligned}\n\t&' + tex + '\\end{aligned}$ \\\\\n\\hline\n')
            f.write('\end{tabular}\n\n\n')

for filename in glob.glob(FILE_GLOB):
    print('Processing ' + filename)
    convertLog(filename)
