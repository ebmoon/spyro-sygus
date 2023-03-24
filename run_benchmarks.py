import argparse
import sys
import os

from property_synthesizer import PropertySynthesizer

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('outfile', nargs='?', type=argparse.FileType('w'), default=sys.stdout)
    parser.add_argument('--verbose', '-v', dest='verbose', action='store_true', default=False)
    parser.add_argument('--disable-min', dest='disable_min', action='store_true', default=False)
    parser.add_argument('--keep-neg-may', dest='keep_neg_may', action='store_true', default=False)
    parser.add_argument('--slv-seed', dest='slv_seed', type=int, nargs='?', default=0)

    args = parser.parse_args(sys.argv[1:])
    outfile = args.outfile
    v = args.verbose
    disable_min = args.disable_min
    keep_neg_may = args.keep_neg_may
    slv_seed = args.slv_seed

    files = [os.path.join(dp, f) for dp, dn, fn in os.walk("./examples") for f in fn if ('.sp' in f)]

    for path in files:
        with open(path, 'r') as infile:
            # if not (('max4' in path) or ('max5' in path) or ('branch.prop' in path)):
            #   continue

            print(path)

            PropertySynthesizer(infile, outfile, v, slv_seed, keep_neg_may).run()

    outfile.close()

if __name__=="__main__":
    main()