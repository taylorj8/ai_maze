import console
import random
import math
import heapq
from maze import MazeGame

N, S, W, E = ('n', 's', 'w', 'e')
move_options = {'up': (N, 0, -1),
                'down': (S, 0, 1),
                'left': (W, -1, 0),
                'right': (E, 1, 0)}


class DFSSolver(MazeGame):
    def __init__(self, maze=None, state='vis', vis_time=0.05):
        super(DFSSolver, self).__init__(maze, state, vis_time)
        self.stack = []

    def choose_move(self):
        if self.mode != 'benchmark':
            console.set_display(self.maze.height*2+1, 0, "Stack: {}".format([cell.xy() for cell in self.stack]))

        # initialise the stack with the start cell if empty
        if not self.stack:
            start_cell = self.maze[self.player]
            self.stack.append(start_cell)

        # delay for visualisation purposes or wait for key press
        self.wait()

        # current cell is the one at the top of the stack.
        current = self.stack[-1]

        # mark the current cell as visited.
        current.visited = True

        # if the current cell is the target, we're done
        if current.xy() == self.target:
            return 'goto', current.x, current.y

        # filter neighbors to include only those:
        #   1. that have not yet been visited
        #   2. that are accessible (i.e. the wall between current and neighbor is absent)
        neighbours = [
            n for n in self.maze.neighbours(current)
            if not n.visited and current.wall_to(n) not in current.walls
        ]

        if neighbours:
            # choose the first accessible neighbor
            next_cell = neighbours[0]
            self.stack.append(next_cell)
            return 'goto', next_cell.x, next_cell.y
        else:
            # backtrack if no accessible, unvisited neighbours are found
            self.stack.pop()
            if self.stack:
                next_cell = self.stack[-1]
                return 'goto', next_cell.x, next_cell.y
            else:
                # no moves left: signal quit
                return 'q', 0, 0

    def replay(self):
        # Print the DFS solution path (i.e. the current stack)
        self.path = self.stack
        self.replay_moves()

class BFSSolver(MazeGame):
    def __init__(self, maze=None, state='vis', vis_time=0.05):
        super(BFSSolver, self).__init__(maze, state, vis_time)
        self.queue = []
        self.parent = {} # dictionary to map cells in the path to their parent - allows to reconstruct the path

    # override the choose move method
    def choose_move(self):
        if self.mode != 'benchmark':
            console.set_display(self.maze.height*2+1, 0, "Queue: {}".format([(cell.xy()) for cell in self.queue]))

        # if the queue is empty, initialise it with the starting cell
        if not self.queue:
            start_cell = self.maze[self.player]
            self.queue.append(start_cell)
            self.parent[start_cell] = None  # starting cell has no parent

        # delay for visualisation purposes or wait for key press
        self.wait()

        # dequeue the first cell
        current = self.queue.pop(0)
        current.visited = True

        # check if the current cell is the target
        if current.xy() == self.target:
            return 'goto', current.x, current.y

        # get all neighbors that:
        #   1. have not been visited
        #   2. are accessible (i.e. the wall between current and neighbour is removed)
        accessible_neighbours = [
            n for n in self.maze.neighbours(current)
            if not n.visited and current.wall_to(n) not in current.walls
        ]

        # enqueue all accessible neighbors
        for neighbour in accessible_neighbours:
            if neighbour.xy() not in self.parent: # only enqueue if not already in the path
                self.parent[neighbour] = current
                self.queue.append(neighbour)

        # if there are still cells in the queue, continue with the next one
        if self.queue:
            next_cell = self.queue[0]
            return 'goto', next_cell.x, next_cell.y
        else:
            # no more moves available - something went wrong
            return 'q', 0, 0

    def replay(self):
        # reconstruct the path from the target to the start
        path = []
        current = self.maze[self.target]
        while current is not None:
            path.append(current)
            current = self.parent.get(current)  # Get the parent of the current cell.
        path.reverse()  # Now path is from start to target.
        self.path = path

        self.replay_moves()


class AStarSolver(MazeGame):
    def __init__(self, maze=None, state='vis', vis_time=0.05):
        super(AStarSolver, self).__init__(maze, state, vis_time)
        self.open_set = []    # Priority queue: each element is a tuple (f_score cell)
        self.parent = {}      # Dictionary mapping a cell to its parent cell (for path reconstruction)
        self.g_score = {}     # Dictionary mapping a cell to its cost from the start

    def heuristic(self, cell, target):
        """
        Compute the Manhattan distance from the given cell to the target cell.
        This serves as the heuristic (h) in A*.
        """
        return abs(cell.x - target.x) + abs(cell.y - target.y)

    def choose_move(self):
        if self.mode != 'benchmark':
            console.set_display(
                self.maze.height*2+1, 0,
                "Open Set: {}".format([cell.xy() for _, cell in self.open_set])
            )

        # if the open set is empty, initialize it with the starting cell
        if not self.open_set:
            start_cell = self.maze[self.player]
            self.g_score[start_cell] = 0
            target_cell = self.maze[self.target]
            f_score = self.g_score[start_cell] + self.heuristic(start_cell, target_cell)
            heapq.heappush(self.open_set, (f_score, start_cell))
            self.parent[start_cell] = None

        # delay for visualisation purposes or wait for key press
        self.wait()

        # pop the cell with the lowest f_score from the open set
        f_current, current = heapq.heappop(self.open_set)
        current.visited = True

        # if the current cell is the target, we're done
        if current.xy() == self.target:
            return 'goto', current.x, current.y

        target_cell = self.maze[self.target]
        # process each neighbour of the current cell
        for neighbour in self.maze.neighbours(current):
            # skip the neighbour if it has been visited or a wall blocks the connection
            if neighbour.visited or current.wall_to(neighbour) in current.walls:
                continue

            # assume the cost between adjacent cells is 1
            tentative_g = self.g_score[current] + 1

            # if the neighbor hasn't been discovered or we found a better path to it...
            if neighbour not in self.g_score or tentative_g < self.g_score[neighbour]:
                self.parent[neighbour] = current
                self.g_score[neighbour] = tentative_g
                f_score = tentative_g + self.heuristic(neighbour, target_cell)
                # push the neighbour with its f_score and a counter as a tie-breaker
                heapq.heappush(self.open_set, (f_score, neighbour))

        # if there are still cells in the open set, set the next move
        if self.open_set:
            next_cell = self.open_set[0][1]  # peek at the cell with the lowest f_score.
            return 'goto', next_cell.x, next_cell.y
        else:
            # no more moves available
            return 'q', 0, 0

    def replay(self):
        """
        Reconstruct and replay the found path from the target back to the start.
        The path is built by following parent pointers and then reversed to display
        the sequence from the starting cell to the target.
        """
        target_cell = self.maze[self.target]
        path = []
        current = target_cell
        while current is not None:
            path.append(current)
            current = self.parent.get(current)  # get the parent of the current cell
        path.reverse()  # now the path is in order from start to target
        self.path = path

        self.replay_moves()


class MDPValueIterationSolver(MazeGame):
    """
    Maze solver that uses Markov Decision Process (MDP) value iteration to
    precompute an optimal policy from every cell to the target.
    """

    def __init__(self, maze=None, state='vis', vis_time=0.01):
        super(MDPValueIterationSolver, self).__init__(maze, state, vis_time)
        self.costs = {} # dictionary mapping each cell to its cost-to-go (V)
        self.policy = {} # dictionary mapping each cell to its best action (one of: 'up', 'down', 'left', 'right')
        self.epoch = 0

    def get_results(self):
        return {
            "maze": f"{self.maze.width}x{self.maze.height}-",
            "algorithm": self.__class__.__name__.replace("Solver", ""),
            "execution_time (s)": self.timer,
            "path_length": len(self.path),
            "peak_memory (kB)": self.peak_memory,
            "epochs": self.epoch
        }

    def compute_policy(self):
        """
        Compute the optimal policy using Policy Iteration.
        In our maze, every allowed move costs 1, and the target cell (goal)
        is a terminal state with cost 0.
        """
        target_cell = self.maze[self.target]

        self.initialise_policy()

        # initialize the value function: cost-to-go from each cell
        self.costs = {cell: 1000 for cell in self.maze.cells}
        self.costs[target_cell] = 0

        convergence_threshold = 0.001

        # main loop - Policy Evaluation then Policy Improvement
        # run until the policy doesn't change, or the maximum number of epochs is reached
        delta = 1
        while delta > convergence_threshold and self.epoch < 10000:
            self.epoch += 1
            delta = self.value_iteration()
            # console.display(f"Epoch {epoch}: highest delta = {delta}")


    def initialise_policy(self):
        # initialize an arbitrary policy
        # randomly choose and action from the valid moves for each cell
        for cell in self.maze.cells:
            if cell == self.maze[self.target]:
                continue  # terminal state - no action needed

            valid_actions = self.get_valid_actions(cell)
            # choose a random valid action if available - otherwise, mark with None
            self.policy[cell] = random.choice(valid_actions) if valid_actions else None


    def value_iteration(self):
        delta = 0
        for cell in self.maze.cells:
            if cell == self.maze[self.target]:
                continue

            best_value = 1000
            best_action = None

            valid_actions = self.get_valid_actions(cell)
            for action in valid_actions:
                _, dx, dy = move_options[action]
                neighbour = self.maze[(cell.x + dx, cell.y + dy)]

                candidate_value = 1 + self.costs[neighbour]
                if candidate_value < best_value:
                    best_value = candidate_value
                    best_action = action

            if best_value < self.costs[cell]:
                delta = max(delta, abs(self.costs[cell] - best_value))
                self.costs[cell] = best_value
                self.policy[cell] = best_action

        return delta


    def choose_move(self):
        """
        Instead of waiting for user key input, this solver looks up the
        optimal action from the precomputed policy for the player's current
        position and returns the corresponding move.
        """
        # if the policy hasn't been computed yet, do it now
        if self.policy == {}:
            self.compute_policy()

        current_cell = self.maze[self.player]
        self.path.append(current_cell)

        # if we have reached the target, return a 'goto' command
        if self.player == self.target:
            return 'goto', current_cell.x, current_cell.y
        # delay for visualisation purposes or wait for key press
        self.wait()

        # retrieve the optimal action from the policy
        action = self.policy.get(current_cell)
        if action is None:
            return 'q', 0, 0

        # return the move tuple
        return move_options[action]


    # append the target to the path for consistency with the search methods
    def replay(self):
        self.path.append(self.maze[self.target])


class MDPPolicyIterationSolver(MazeGame):
    """
    Maze solver that uses Policy Iteration to precompute an optimal policy.

    Policy Iteration consists of two main steps:
      1. Policy Evaluation: Given a policy, compute the cost-to-go (value function)
         for every state.
      2. Policy Improvement: Update the policy by choosing at each state the action
         that minimizes the cost (i.e. yields the lowest value).

    These two steps are repeated until no change is made to the policy.
    """

    def __init__(self, maze=None, state='vis', vis_time=0.01):
        super(MDPPolicyIterationSolver, self).__init__(maze, state, vis_time)
        self.policy = {}
        self.costs = {}
        self.epoch = 0

    def get_results(self):
        return {
            "maze": f"{self.maze.width}x{self.maze.height}-",
            "algorithm": self.__class__.__name__.replace("Solver", ""),
            "execution_time (s)": self.timer,
            "path_length": len(self.path),
            "peak_memory (kB)": self.peak_memory,
            "epochs": self.epoch
        }

    def compute_policy(self):
        """
        Compute the optimal policy using Policy Iteration.
        In our maze, every allowed move costs 1, and the target cell (goal)
        is a terminal state with cost 0.
        """
        target_cell = self.maze[self.target]

        self.initialise_policy()

        # initialize the value function: cost-to-go from each cell
        self.costs = {cell: math.inf for cell in self.maze.cells}
        self.costs[target_cell] = 0

        # main loop - Policy Evaluation then Policy Improvement
        # run until the policy doesn't change, or the maximum number of epochs is reached
        actions_updated = 1
        while actions_updated > 0 and self.epoch < 10000:
            self.epoch += 1
            self.evaluate_policy()
            actions_updated = self.improve_policy()
            # console.display(f"Epoch {epoch}: Updated {actions_updated} actions.")


    def initialise_policy(self):
        # initialize an arbitrary policy
        # randomly choose and action from the valid moves for each cell
        for cell in self.maze.cells:
            if cell == self.maze[self.target]:
                continue  # terminal state - no action needed

            valid_actions = self.get_valid_actions(cell)
            # choose a random valid action if available - otherwise, mark with None
            self.policy[cell] = random.choice(valid_actions) if valid_actions else None


    def evaluate_policy(self):
        epoch = 0
        delta = 1
        # repeat until no changes occur or for 500 epochs
        while epoch < 500 and delta > 0:
            epoch += 1
            delta = 0
            for cell in self.maze.cells:
                if cell == self.maze[self.target]:
                    continue
                action = self.policy[cell]
                # compute position of cell after action taken
                _, dx, dy = move_options[action]
                neighbour = self.maze[(cell.x + dx, cell.y + dy)]

                # the new cost is the cost of the neighbouring cell + 1
                # no discount factor used as I am trying to find the shortest path
                new_cost = 1 + self.costs[neighbour]
                delta = max(delta, abs(self.costs[cell] - new_cost))
                self.costs[cell] = new_cost


    def improve_policy(self):
        actions_updated = 0
        for cell in self.maze.cells:
            if cell == self.maze[self.target]:
                continue
            old_action = self.policy.get(cell)
            best_action = old_action
            best_value = math.inf

            valid_actions = self.get_valid_actions(cell)
            for action in valid_actions:
                _, dx, dy = move_options[action]
                neighbour = self.maze[(cell.x + dx, cell.y + dy)]

                candidate_value = 1 + self.costs[neighbour]
                if candidate_value < best_value:
                    best_value = candidate_value
                    best_action = action
            if best_action != old_action:
                self.policy[cell] = best_action
                actions_updated += 1
        return actions_updated


    def choose_move(self):
        """
        Uses the precomputed optimal policy to choose the next move.
        Returns a move command for the MazeGame (or quits if no valid move exists).
        """

        # if the policy hasn't been computed yet, do it now
        if self.policy == {}:
            self.compute_policy()

        current_cell = self.maze[self.player]
        self.path.append(current_cell)
        if self.player == self.target:
            return 'goto', current_cell.x, current_cell.y

        # delay for visualisation purposes or wait for key press
        self.wait()

        action = self.policy.get(current_cell)
        if action is None:
            return 'q', 0, 0
        return move_options[action]


    # append the target to the path for consistency with the search methods
    def replay(self):
        self.path.append(self.maze[self.target])
