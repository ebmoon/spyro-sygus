import os
import numpy as np
import shutil
import statistics

from property_synthesizer import PropertySynthesizer

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

def run_benchmark(files, outfile_name, seeds, nofreeze = False, write_result_files = False):
    os.makedirs("results", exist_ok=True)
    for seed in seeds:
        outfile_basename = outfile_name if len(seeds) <= 1 else f"{outfile_name}_{seed}"
        outfile = open(f"results/{outfile_basename}.csv", "w")
        statistics_list = []

        for path in files:
            filename = os.path.splitext(path)[0]

            infile = open(f"benchmarks/{path}", 'r')

            phi_list, statistics = PropertySynthesizer(infile, outfile, False, seed, nofreeze).run()

            print(f"Done: {filename}, seed = {seed}, nofreeze = {nofreeze}")

            if write_result_files:
                path = f"results/{filename}_{seed}.txt"
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, "w") as f:
                    for n, phi in enumerate(phi_list):
                        f.write(f"Property {n}\n\n")
                        f.write(str(phi))
                        f.write("\n\n")

            statistics_str = [str(x) if isinstance(x, int) else f"{x:.2f}" for x in statistics]
            statistics_list.append([filename] + statistics_str)

            infile.close()
    
        outfile.write(",".join(columns) + "\n")
        for statistics in statistics_list:
            outfile.write(",".join(statistics) + "\n")
        
        outfile.close()

def compute_median(filename, seeds, copyfile = False):
    files = [f"results/{filename}_{seed}.csv" for seed in seeds]
    benchmarks = {}

    for path in files:
        with open(path, 'r') as f:
            lines = f.readlines()

        for line in lines[1:]:
            data = [s.strip() for s in line.split(',')]

            name = data[0]
            stat = data[1:]
            stat = [float(x) for x in stat]

            if name in benchmarks.keys():
                benchmarks[name].append(stat)
            else:
                benchmarks[name] = [stat]

    medians = {}
    for name, stat in benchmarks.items():
        data = []
        stat = np.array(stat).T.tolist()

        for column in stat:
            if len(column) == 3:
                data.append(statistics.median(column))

        if len(data) == 0:
            continue

        medians[name] = data

    with open(f"results/{filename}_median.csv", 'w') as f:
        f.write(",".join(columns) + "\n")
        for name in benchmarks.keys():
            for n, stat in enumerate(benchmarks[name]):
                if stat[-1] == medians[name][-1]:
                    stat = [str(x) for x in stat]
                    f.write(','.join([name] + stat) + '\n')

                    if copyfile:
                        seed = seeds[n]
                        shutil.copy(f"results/{name}_{seed}.txt", f"results/{name}_median.txt")
                    
                    break

def main():
    files = [
        "sygus/max2.sp",
        "sygus/max3.sp",
        "sygus/array_search_2.sp",
        "sygus/diff.sp",
        "arithmetic/abs1.sp",
        "arithmetic/abs3.sp"
    ]

    seeds = [32, 64, 128]
    run_benchmark(files, "smt_default", seeds, False, True)
    run_benchmark(files, "smt_nofreeze", seeds, True, False)
    compute_median("smt_default", seeds, True)
    compute_median("smt_nofreeze", seeds)

if __name__=="__main__":
    main()