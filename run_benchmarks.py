import argparse
import sys
import os

from property_synthesizer import PropertySynthesizer

def main():
    parser = argparse.ArgumentParser()

    outfile_default = open("results/table_default.csv", "w")
    outfile_keepmay = open("results/table_without_freeze.csv", "w")

    args = parser.parse_args(sys.argv[1:])

    files = [os.path.join(dp, f) for dp, dn, fn in os.walk("./examples") for f in fn if ('.sp' in f)]
    
    columns = [
        "benchmark_name",
        "num_conjunct", 
        "num_synth_call", 
        "time_synth_call", 
        "num_soundness_call", 
        "time_soundness_call", 
        "num_precision_call",
        "time_precision_call",
        "time_last_call",
        "time_last_iter",
        "time_total"
    ]
    pass_list = ["abs2", "array_search_3", "diff_twice", "max4"]
    seeds = {
        "max2": 64,
        "max3": 64,
        "array_search_2": 128,
        "diff": 64,
        "abs1": 64,
        "abs3": 64
    }
    keepneg_seeds = {
        "max2": 32,
        "max3": 32,
        "array_search_2": 128,
        "diff": 128,
        "abs1": 128,
        "abs3": 64
    }
    statistics_default_list = []
    statistics_nofreeze_list = []

    for path in files:
        filename = os.path.basename(path)
        filename = os.path.splitext(filename)[0]

        if filename in pass_list:
            statistics_str = ["-"] * (len(columns) - 1)
            statistics_default_list.append([filename] + statistics_str)
            statistics_nofreeze_list.append([filename] + statistics_str)
            continue

        with open(path, 'r') as infile:
            seed = seeds[filename]
            phi_list, statistics = PropertySynthesizer(infile, outfile_default, False, seed, False).run()

            with open(f"results/{filename}.txt", "w") as f:
                for n, phi in enumerate(phi_list):
                    f.write(f"Property {n}\n\n")
                    f.write(str(phi))
                    f.write("\n\n")

            statistics_str = [str(x) if isinstance(x, int) else f"{x:.2f}" for x in statistics]
            statistics_default_list.append([filename] + statistics_str)

        with open(path, 'r') as infile:
            phi_list, statistics = PropertySynthesizer(infile, outfile_keepmay, False, seed, True).run()

            statistics_str = [str(x) if isinstance(x, int) else f"{x:.2f}" for x in statistics]
            statistics_nofreeze_list.append([filename] + statistics_str)

        print(f"{filename}: Done")

    outfile_default.write(",".join(columns) + "\n")
    for statistics in statistics_default_list:
        outfile_default.write(",".join(statistics) + "\n")

    outfile_default.close()

    outfile_keepmay.write(",".join(columns) + "\n")
    for statistics in statistics_nofreeze_list:
        outfile_keepmay.write(",".join(statistics) + "\n")

    outfile_keepmay.close()

if __name__=="__main__":
    main()