import random
import console
import time
import tracemalloc


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
        self.path = []
        self.player = None
        self.target = None
        self.vis_time = vis_time
        self.mode = state  # decides whether to delay, wait for keypress or not wait at all
        self.timer = None
        self.peak_memory = None
        self.move_counter = 0

    def get_results(self):
        return {
            "maze": f"{self.maze.width}x{self.maze.height}-",
            "algorithm": self.__class__.__name__.replace("Solver", ""),
            "execution_time (s)": self.timer,
            "path_length": len(self.path),
            "peak_memory (kB)": self.peak_memory,
            "total_moves": self.move_counter
        }

    def generate_maze(self, width, height):
        self.maze = Maze.generate(width, height)
        self.player = self._get_random_position()
        self.target = self._get_random_position()

    def set_maze(self, maze):
        self.maze = maze
        self.player = (0, 0)
        self.target = (maze.width - 1, maze.height - 1)

    def _get_random_position(self):
        """
        Returns a random position on the maze.
        """
        return self.maze.get_random_position()

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

    def _display(self, pos, value):
        """
        Displays a value on the screen from an x and y maze positions.
        """
        x, y = pos
        # Double x position because displayed maze is double-wide.
        console.set_display(y * 2 + 1, x * 4 + 2, value)

    def play(self, show_stats=True):
        """
        Starts an interactive game on this maze, with random starting and goal
        positions. Returns True if the user won, or False if she quit the game
        by pressing "q".
        """

        if self.maze is None:
            self.maze = Maze.generate(20, 10)

        self.timer = time.time()

        if self.mode == 'benchmark':
            console.display(f"Benchmarking {self.__class__.__name__} on {self.maze.width}x{self.maze.height} maze...")

        tracemalloc.start()
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
        _, self.peak_memory = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        self.peak_memory = self.peak_memory / 3 ** 10  # convert to kB

        self.timer = time.time() - self.timer
        self.replay()

        if self.__class__.__name__.startswith('MDP'):
            unique_metric = f"Total epochs: {self.epoch}\n"
        else:
            unique_metric = f"Unique cells visited: {len([cell for cell in self.maze.cells if cell.visited])}\n"
        # moves_str = ", ".join([f"({cell.x}, {cell.y})" for cell in self.path])

        if show_stats:
            console.display(f"{self.__class__.__name__} took {self.timer:.5f} seconds.\n"
                            f"Shortest path found was {len(self.path) - 1} moves.\n" + unique_metric +
                            f"Peak memory usage: {self.peak_memory:.3f} KB.")
            console.get_key()
        self.maze.reset()

    def choose_move(self):
        key = console.get_valid_key(['up', 'down', 'left', 'right', 'q'])

        if key == 'q':
            return False

        # self.path.append(key)
        return move_options[key]

    # don't need to replay when playing interactively
    def replay(self):
        pass

    def replay_moves(self):
        if self.mode != 'benchmark':
            for cell in self.path:
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