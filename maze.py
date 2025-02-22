# -*- coding: utf-8 -*-
import random
import time
import heapq
import math
import csv


# Easy to read representation for each cardinal direction.
N, S, W, E = ('n', 's', 'w', 'e')
move_options = {'up': (N, 0, -1),
                'down': (S, 0, 1),
                'left': (W, -1, 0),
                'right': (E, 1, 0)}

not_wall = [' ', '.', 'x']

class Cell(object):
    """
    Class for each individual cell. Knows only its position and which walls are
    still standing.
    """
    def __init__(self, x, y, walls):
        self.x = x
        self.y = y
        self.walls = set(walls)
        self.visited = False

    def __repr__(self):
        # <15, 25 (es  )>
        return '({}, {})'.format(self.x, self.y)

    def __contains__(self, item):
        # N in cell
        return item in self.walls

    def __lt__(self, other):
        return (self.x, self.y) < (other.x, other.y)

    def xy(self):
        return self.x, self.y

    def is_full(self):
        """
        Returns True if all walls are still standing.
        """
        return len(self.walls) == 4

    def wall_to(self, other):
        """
        Returns the direction to the given cell from the current one.
        Must be one cell away only.
        """
        assert abs(self.x - other.x) + abs(self.y - other.y) == 1, '{}, {}'.format(self, other)
        if other.y < self.y:
            return N
        elif other.y > self.y:
            return S
        elif other.x < self.x:
            return W
        elif other.x > self.x:
            return E
        else:
            assert False

    def connect(self, other):
        """
        Removes the wall between two adjacent cells.
        """
        other.walls.remove(other.wall_to(self))
        self.walls.remove(self.wall_to(other))

class Maze(object):
    """
    Maze class containing full board and maze generation algorithms.
    """

    # Unicode character for a wall with other walls in the given directions.
    UNICODE_BY_CONNECTIONS = {'ensw': '┼',
                              'ens': '├',
                              'enw': '┴',
                              'esw': '┬',
                              'es': '┌',
                              'en': '└',
                              'ew': '─',
                              'e': '╶',
                              'nsw': '┤',
                              'ns': '│',
                              'nw': '┘',
                              'sw': '┐',
                              's': '╷',
                              'n': '╵',
                              'w': '╴',
                              '': ' '}

    def __init__(self, width=20, height=10):
        """
        Creates a new maze with the given sizes, with all walls standing.
        """
        self.width = width
        self.height = height
        self.cells = []
        for y in range(self.height):
            for x in range(self.width):
                self.cells.append(Cell(x, y, [N, S, E, W]))

    def __getitem__(self, index):
        """
        Returns the cell at index = (x, y).
        """
        x, y = index
        if 0 <= x < self.width and 0 <= y < self.height:
            return self.cells[x + y * self.width]
        else:
            return None

    def reset(self):
        for cell in self.cells:
            cell.visited = False

    def neighbours(self, cell):
        """
        Returns the list of neighboring cells, not counting diagonals. Cells on
        borders or corners may have less than 4 neighbors.
        """
        x = cell.x
        y = cell.y
        for new_x, new_y in [(x, y - 1), (x, y + 1), (x - 1, y), (x + 1, y)]:
            neighbour = self[new_x, new_y]
            if neighbour is not None:
                yield neighbour

    def _to_str_matrix(self):
        """
        Returns a matrix with a pretty printed visual representation of this
        maze. Example 5x5:

        OOOOOOOOOOO
        O       O O
        OOO OOO O O
        O O   O   O
        O OOO OOO O
        O   O O   O
        OOO O O OOO
        O   O O O O
        O OOO O O O
        O     O   O
        OOOOOOOOOOO
        """
        str_matrix = [['O'] * (self.width * 2 + 1)
                      for i in range(self.height * 2 + 1)]

        for cell in self.cells:
            x = cell.x * 2 + 1
            y = cell.y * 2 + 1
            str_matrix[y][x] = ' '
            if N not in cell and y > 0:
                str_matrix[y - 1][x + 0] = ' '
            if S not in cell and y + 1 < self.width:
                str_matrix[y + 1][x + 0] = ' '
            if W not in cell and x > 0:
                str_matrix[y][x - 1] = ' '
            if E not in cell and x + 1 < self.width:
                str_matrix[y][x + 1] = ' '

        return str_matrix

    def __repr__(self):
        """
        Returns an Unicode representation of the maze. Size is doubled
        horizontally to avoid a stretched look. Example 5x5:

        ┌───┬───────┬───────┐
        │   │       │       │
        │   │   ╷   ╵   ╷   │
        │   │   │       │   │
        │   │   └───┬───┘   │
        │   │       │       │
        │   └───────┤   ┌───┤
        │           │   │   │
        │   ╷   ╶───┘   ╵   │
        │   │               │
        └───┴───────────────┘
        """
        # Starts with regular representation. Looks stretched because chars are
        # twice as high as they are wide (look at docs example in
        # `Maze._to_str_matrix`).
        skinny_matrix = self._to_str_matrix()

        # Simply duplicate each character in each line.
        double_wide_matrix = []
        for line in skinny_matrix:
            double_wide_matrix.append([])
            for char in line:
                double_wide_matrix[-1].append(char)
                double_wide_matrix[-1].append(char)

        # The last two chars of each line are walls, and we will need only one.
        # So we remove the last char of each line.
        matrix = [line[:-1] for line in double_wide_matrix]

        def g(x, y):
            """
            Returns True if there is a wall at (x, y). Values outside the valid
            range always return false.

            This is a temporary helper function.
            """
            if 0 <= x < len(matrix[0]) and 0 <= y < len(matrix):
                return matrix[y][x] != ' '
            else:
                return False

        # Fix double wide walls, finally giving the impression of a symmetric
        # maze.
        for y, line in enumerate(matrix):
            for x, char in enumerate(line):
                if not g(x, y) and g(x - 1, y):
                    matrix[y][x - 1] = ' '

        # Right now the maze has the correct aspect ratio, but is still using
        # 'O' to represent walls.

        # Finally we replace the walls with Unicode characters depending on
        # their context.
        for y, line in enumerate(matrix):
            for x, char in enumerate(line):
                if not g(x, y):
                    continue

                connections = {N, S, E, W}
                if not g(x, y + 1): connections.remove(S)
                if not g(x, y - 1): connections.remove(N)
                if not g(x + 1, y): connections.remove(E)
                if not g(x - 1, y): connections.remove(W)

                str_connections = ''.join(sorted(connections))
                # Note we are changing the matrix we are reading. We need to be
                # careful as to not break the `g` function implementation.
                try:
                    matrix[y][x] = Maze.UNICODE_BY_CONNECTIONS[str_connections]
                except:
                    console.display(f"Error at {x}, {y} with connections {str_connections}")
                    console.get_key()

        # Simple double join to transform list of lists into string.
        return '\n'.join(''.join(line) for line in matrix) + '\n'

    def randomize(self):
        """
        Knocks down random walls to build a random perfect maze.

        Algorithm from http://mazeworks.com/mazegen/mazetut/index.htm
        """
        cell_stack = []
        cell = random.choice(self.cells)
        n_visited_cells = 1

        i = 0
        while n_visited_cells < len(self.cells):
            neighbours = [c for c in self.neighbours(cell) if c.is_full()]
            if len(neighbours):
                neighbor = random.choice(neighbours)
                cell.connect(neighbor)
                cell_stack.append(cell)
                cell = neighbor
                n_visited_cells += 1
            else:
                cell = cell_stack.pop()


    def remove_random_walls(self, n_walls):
        # remove n_walls random walls to create a maze that has multiple paths to the target
        random_cells = random.sample(self.cells, n_walls)
        for cell in random_cells:
            neighbours = [c for c in self.neighbours(cell) if cell.wall_to(c) in cell.walls]
            if neighbours:
                neighbour = random.choice(neighbours)
                cell.connect(neighbour)


    @staticmethod
    def generate(width=20, height=10):
        """
        Returns a new random perfect maze with the given sizes.
        """
        m = Maze(width, height)
        m.randomize()
        m.remove_random_walls(width * height // 20) # remove an extra wall from 5% of the cells
        return m

    def get_random_position(self):
        """
        Returns a random position on the maze.
        """
        return random.choice(self.cells).xy()


class MazeGame(object):
    """
    Class for interactively playing random maze games.
    """
    def __init__(self, maze=None, state='vis', vis_time=0.05):
        self.maze = maze
        self.moves = []
        self.player = None
        self.target = None
        self.vis_time = vis_time
        self.mode = state # decides whether to delay, wait for keypress or not wait at all
        self.move_counter = 0
        self.timer = None


    def generate_maze(self, width, height):
        self.maze = Maze.generate(width, height)
        self.player = self._get_random_position()
        self.target = self._get_random_position()

    def set_maze(self, maze, player, target):
        self.maze = maze
        self.player = player
        self.target = target

    def _get_random_position(self):
        """
        Returns a random position on the maze.
        """
        return self.maze.get_random_position()

    def _display(self, pos, value):
        """
        Displays a value on the screen from an x and y maze positions.
        """
        x, y = pos
        # Double x position because displayed maze is double-wide.
        console.set_display(y * 2 + 1, x * 4 + 2, value)

    def play(self):
        """
        Starts an interactive game on this maze, with random starting and goal
        positions. Returns True if the user won, or False if she quit the game
        by pressing "q".
        """

        if self.maze is None:
            self.maze = Maze.generate(20, 10)
            
        self.timer = time.time()

        if self.mode == 'benchmark':
            console.display("Benchmarking {}...".format(self.__class__.__name__))

        while self.player != self.target:
            if self.mode != 'benchmark':
                console.display(str(self.maze))
                for cell in filter(lambda c: c.visited, self.maze.cells):
                    self._display(cell.xy(), 'x')
                self._display(self.player, '@')
                self._display(self.target, '$')

            direction, x, y = self.choose_move()
            self.move_counter += 1

            current_cell = self.maze[self.player]
            if direction == 'goto':
                self.player = (x, y)
            elif direction not in current_cell:
                self.player = (self.player[0] + x, self.player[1] + y)

        self.replay()
        self.timer = time.time() - self.timer

        moves_str = ", ".join([f"({cell.x}, {cell.y})" for cell in self.moves])
        # console.display('Shortest path found was {} moves.'.format(self.move_counter, len(self.moves)) + "\n" + moves_str)
        console.display('{} took {:.5f} seconds.'.format(self.__class__.__name__, self.timer))
        console.get_key()
        maze.reset()
        return self.timer

    def choose_move(self):
        key = console.get_valid_key(['up', 'down', 'left', 'right', 'q'])

        if key == 'q':
            return False

        # self.moves.append(key)
        return move_options[key]

    # don't need to replay when playing interactively
    def replay(self):
        pass

    def replay_moves(self):
        if self.mode != 'benchmark':
            for cell in self.moves:
                time.sleep(self.vis_time)
                console.display(str(self.maze))
                self._display(self.player, '@')
                self._display(self.target, '$')
                self.player = cell.xy()

    def wait(self):
        # delay for visualisation purposes or wait for key press
        match self.mode:
            case 'vis':
                time.sleep(self.vis_time)
            case 'key':
                console.get_key()
            case 'benchmark':
                pass


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
        self.moves = self.stack
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
        self.moves = path

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
        self.moves = path

        self.replay_moves()


class MDPValueIterationSolver(MazeGame):
    """
    Maze solver that uses Markov Decision Process (MDP) value iteration to
    precompute an optimal policy from every cell to the target.
    """

    def __init__(self, maze=None, state='vis', vis_time=0.05):
        super(MDPValueIterationSolver, self).__init__(maze, state, vis_time)
        self.V = {} # dictionary mapping each cell to its cost-to-go (V)
        self.policy = {} # dictionary mapping each cell to its best action (one of: 'up', 'down', 'left', 'right')

    def compute_policy(self):
        """
        Run value iteration over all maze cells to compute the optimal cost-to-go
        (V) and a corresponding policy that indicates the best move from each cell.
        Each allowed move has a cost of 1. The target cell has V = 0.
        """
        # initialize the value function: set every cell’s cost to infinity
        # except for the target cell
        self.V = {cell: math.inf for cell in self.maze.cells}
        target_cell = self.maze[self.target]
        self.V[target_cell] = 0

        # value iteration loop: update V(s) for all cells until values converge
        converged = False
        while not converged:
            converged = True  # assume convergence; will be set to False if any update occurs
            # iterate over all cells in the maze
            for cell in self.maze.cells:
                # the target is our terminal state
                if cell == target_cell:
                    continue

                best_value = math.inf
                best_action = None

                # try every possible action from this cell
                for action, (_, dx, dy) in move_options.items():
                    nx = cell.x + dx
                    ny = cell.y + dy
                    # check that the neighbour coordinate is within the maze bounds
                    if not (0 <= nx < self.maze.width and 0 <= ny < self.maze.height):
                        continue
                    neighbour = self.maze[(nx, ny)]
                    # check if a wall blocks the move from cell to neighbour
                    if cell.wall_to(neighbour) in cell.walls:
                        continue

                    # the cost to move is 1 plus the cost-to-go from the neighbour
                    candidate_value = 1 + self.V[neighbour]
                    if candidate_value < best_value:
                        best_value = candidate_value
                        best_action = action

                # if we found a better value than the current one, update it
                if abs(self.V[cell] - best_value) > 1e-6:
                    self.V[cell] = best_value
                    self.policy[cell] = best_action
                    converged = False


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

        # delay for visualisation purposes or wait for key press
        self.wait()

        # if we have reached the target, return a 'goto' command
        if self.player == self.target:
            return 'goto', current_cell.x, current_cell.y

        # retrieve the optimal action from the policy
        action = self.policy.get(current_cell)
        if action is None:
            return 'q', 0, 0

        # return the move tuple
        return move_options[action]


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

    def __init__(self, maze=None, state='vis', vis_time=0.5):
        super(MDPPolicyIterationSolver, self).__init__(maze, state, vis_time)
        self.policy = {}
        self.costs = {}

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
        epoch = 0
        actions_updated = 1
        while actions_updated > 0 and epoch < 10000:
            epoch += 1
            self.evaluate_policy()
            actions_updated = self.improve_policy()
            console.display(f"Epoch {epoch}: Updated {actions_updated} actions.")


    def get_valid_actions(self, cell):
        valid_actions = []
        for action, (_, dx, dy) in move_options.items():
            nx, ny = cell.x + dx, cell.y + dy
            if not (0 <= nx < self.maze.width and 0 <= ny < self.maze.height):
                continue
            neighbour = self.maze[(nx, ny)]
            # check for a wall blocking the move
            if cell.wall_to(neighbour) in cell.walls:
                continue
            valid_actions.append(action)
        return valid_actions


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
        if self.player == self.target:
            return 'goto', current_cell.x, current_cell.y

        # delay for visualisation purposes or wait for key press
        self.wait()

        action = self.policy.get(current_cell)
        if action is None:
            return 'q', 0, 0
        return move_options[action]


def append_to_csv(results, csv_file_path='results.csv'):
    """
    Appends the timing results of an algorithm run to a CSV file.

    Parameters:
    algorithm_name (str): The name of the algorithm.
    time_taken (float): The time taken by the algorithm.
    csv_file_path (str): The path to the CSV file.
    """
    with open(csv_file_path, mode='a', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(results)


if __name__ == '__main__':
    import sys
    solvers = []
    if len(sys.argv) > 1:
        args = sys.argv[1:]
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

    # give all solvers the same maze
    maze = Maze.generate(width, height)
    player = maze.get_random_position()
    target = maze.get_random_position()
    for solver in solvers:
        solver.set_maze(maze, player, target)

    results = []

    import console
    try:
        for solver in solvers:
            time_taken = solver.play()
            results.append(time_taken)
    except:
        import traceback
        traceback.print_exc(file=open('error_log.txt', 'a'))

    append_to_csv(results)
