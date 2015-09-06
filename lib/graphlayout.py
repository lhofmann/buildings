#
# This script provides an interface between MAGMA and the NetworkX library
# See function PythonSpringLayout in buildingQuotient.m for details
#
# Requires NetworkX (https://networkx.github.io) to be installed
#

import networkx as nx
import argparse, os.path, sys

class ArgParser(argparse.ArgumentParser):
    def error(self, message):
        sys.stderr.write('error: %s\n' % message)
        self.print_help()
        sys.exit(2)

def main():
    parser = ArgParser()
    parser.add_argument('inputFilename', metavar='INFILE', action='store', help='Input edgelist filename')
    parser.add_argument('outputFilename', metavar='OUTFILE', action='store', help='Output filename')
    parser.add_argument('-i', '--iterations', metavar='N', dest='iterations', default=100, type=int, action='store', help='Number of iterations (default: 100)') 
    parser.add_argument('-s', '--scale', metavar='S', dest='scale', default=10.0, type=float, action='store', help='Scale factor (default: 10.0)') 
    parser.add_argument('-d', '--dimension', metavar='S', dest='dimension', default=3, type=int, action='store', help='Dimension (default: 3)') 
    options = parser.parse_args()

    if not os.path.isfile(options.inputFilename):
        sys.stderr.write('error: input file does not exist\n')
        sys.exit(1)

    try:
        G = nx.read_edgelist(options.inputFilename)
    except:
        sys.stderr.write('error reading input file\n')
        sys.exit(1)        

    print('Read graph with {0} nodes and {1} edges.'.format(G.number_of_nodes(), G.number_of_edges()))

    pos = nx.spring_layout(G, dim=options.dimension, iterations=options.iterations, scale=options.scale, k=1/(G.number_of_nodes()**.57))

    with open(options.outputFilename, 'w') as f:
        for node, position in pos.items():
            positions = ' '.join(['{0:.8f}'.format(pos) for pos in position])
            f.write('{0} {1}\n'.format(node, positions))

if __name__ == "__main__":
    main()