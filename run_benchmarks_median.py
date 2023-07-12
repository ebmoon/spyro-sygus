import os

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

def run_benchmark(files, outfile_name, nofreeze = False, write_result_files = False):
    os.makedirs("results", exist_ok=True)
    outfile = open(f"results/{outfile_name}_median.csv", "w")
    statistics_list = []

    for (path, default_seed, nofreeze_seed) in files:
        filename = os.path.splitext(path)[0]
        seed = nofreeze_seed if nofreeze else default_seed

        infile = open(f"benchmarks/{path}", 'r')

        phi_list, statistics = PropertySynthesizer(infile, outfile, False, seed, nofreeze).run()

        print(f"Done: {filename}, seed = {seed}, nofreeze = {nofreeze}")

        if write_result_files:
            path = f"results/{filename}_median.txt"
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

def main():
    files = [
        ("sygus/max2.sp", 128, 32),
        ("sygus/max3.sp", 64, 128),
        ("sygus/array_search_2.sp", 64, 64),
        ("sygus/diff.sp", 64, 32),
        ("arithmetic/abs1.sp", 32, 128),
        ("arithmetic/abs3.sp", 128, 128)
    ]

    seeds = [32, 64, 128]
    run_benchmark(files, "smt_default", False, True)
    run_benchmark(files, "smt_nofreeze", True, False)

if __name__=="__main__":
    main()