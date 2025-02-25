import sys
import subprocess
import traceback
import os
import csv
from maze import Maze
from solvers import *


def get_file_name():
    counter = 0
    while True:
        file_name = f"results{counter}.csv"
        if not os.path.exists(file_name):
            return file_name
        counter += 1


def append_to_csv(results, csv_file_path='results.csv'):

    with open(csv_file_path, 'a', newline='') as csv_file:
        field_names = ["maze", "algorithm", "execution_time (s)", "peak_memory (kB)", "path_length", "total_moves", "epochs"]
        writer = csv.DictWriter(csv_file, fieldnames=field_names)

        if csv_file.tell() == 0:
            writer.writeheader()  # Write the column headers
        writer.writerow(results)


if __name__ == '__main__':
    solvers = []
    args = sys.argv

    if args[1] == '-benchmark':
        try:
            start_size = int(args[2])
            end_size = int(args[3]) + 1
            for i in range(start_size, end_size, 10):
                maze_size = str(i)
                subprocess.run(["python", "main.py", "-s", "all", "-w", maze_size, "-h", maze_size, "-b", "-l"])
            console.display("Benchmarking complete. Results saved to results.csv.")
        except:
            console.display("Usage: python maze.py -benchmark <start_size> <end_size>")
        console.get_key()
        exit()

    if len(args) > 1:
        try:
            if '-w' in args:
                width = int(args[args.index('-w') + 1])
            else:
                width = 20
            if '-h' in args:
                height = int(args[args.index('-h') + 1])
            else:
                height = 10
            if '-s' in args:
                solver_map = {
                    'dfs': DFSSolver(),
                    'bfs': BFSSolver(),
                    'astar': AStarSolver(),
                    'mdpi': MDPValueIterationSolver(),
                    'mdpp': MDPPolicyIterationSolver()
                }
                for arg in args[args.index('-s') + 1:]:
                    if arg == "all":
                        solvers = list(solver_map.values())
                        break
                    elif arg.startswith('-'):
                        break
                    elif arg in solver_map:
                        solvers.append(solver_map[arg])
            else:
                solvers.append(DFSSolver())
            if '-i' in args:
                for solver in solvers:
                    solver.mode = 'key'
            elif '-b' in args:
                for solver in solvers:
                    solver.mode = 'benchmark'
        except:
            print("Usage: python maze.py -w <width> -h <height> -s <solvers> -i/-b")
            exit()
    else:
        solvers.append(DFSSolver())
        width = 20
        height = 10

    # set the random seed for reproducibility
    seed = random.randint(0, 1000000)
    random.seed(seed)

    # give all solvers the same maze
    maze = Maze.generate(width, height)
    for solver in solvers:
        solver.set_maze(maze)

    logging = '-l' in args
    results_file = get_file_name()

    try:
        for solver in solvers:
            solver.play(not logging)
            if logging:
                results = solver.get_results()
                results['maze'] = results['maze'] + str(seed)
                append_to_csv(results, results_file)
    except:
        console.display(traceback.format_exc())
        traceback.print_exc(file=open('error_log.txt', 'a'))
        console.get_key()