import math, deques, heapqueue, sets, hashes, algorithm, strutils, strformat, times, os

type
   PuzzleAction = enum
      Initial, Left, Right, Up, Down

   PuzzleState = ref object
      ## The object that represents the Puzzle
      n, cost, hash: int
      parent: PuzzleState
      action: PuzzleAction
      board: seq[int]
      children: seq[PuzzleState]
      blankRow, blankCol: int

proc newPuzzleState(board: seq[int], n: int, parent: PuzzleState = nil, action = Initial, cost = 0): PuzzleState =
   assert n * n == len(board) and n >= 2, "the length of board is not correct!"
   new result
   result.n = n
   result.cost = cost
   result.hash = hash(board)
   result.parent = parent
   result.action = action
   shallowCopy result.board, board
   result.children = @[]
   for i, item in result.board:
      if item == 0:
         result.blankRow = i div result.n
         result.blankCol = i mod result.n
         break

proc `==`(self, other: PuzzleState): bool =
   if self.isNil: other.isNil
   elif other.isNil: false
   else: self.hash == other.hash

proc hash(self: PuzzleState): Hash = self.hash

proc `<`(self, other: PuzzleState): bool =
   self.cost < other.cost

iterator childrenOf(self: PuzzleState): PuzzleState =
   for i in countdown(self.children.high, 0):
      yield self.children[i]

proc getSolution(self: PuzzleState): seq[PuzzleAction] =
   # Produce a backtrace of the actions taken to find the goal state.
   var step = self
   while step.parent != nil:
      result.add step.action
      step = step.parent
   result.reverse()

proc display(self: PuzzleState) =
   for i in 0 ..< self.n:
      var line = ""
      let offset = i * self.n
      for j in 0 ..< self.n:
         line.add(self.board[offset + j])
         line.add(", ")
      echo line

proc moveLeft(self: PuzzleState): PuzzleState =
   if self.blankCol == 0:
      result = nil
   else:
      let blankIndex = self.blankRow * self.n + self.blankCol
      let target = blankIndex - 1
      var newBoard = self.board
      swap(newBoard[blankIndex], newBoard[target])
      result = newPuzzleState(newBoard, self.n, self, Left, self.cost + 1)

proc moveRight(self: PuzzleState): PuzzleState =
   if self.blankCol == self.n - 1:
      result = nil
   else:
      let blankIndex = self.blankRow * self.n + self.blankCol
      let target = blankIndex + 1
      var newBoard = self.board
      swap(newBoard[blankIndex], newBoard[target])
      result = newPuzzleState(newBoard, self.n, self, Right, self.cost + 1)

proc moveUp(self: PuzzleState): PuzzleState =
   if self.blankRow == 0:
      result = nil
   else:
      let blankIndex = self.blankRow * self.n + self.blankCol
      let target = blankIndex - self.n
      var newBoard = self.board
      swap(newBoard[blankIndex], newBoard[target])
      result = newPuzzleState(newBoard, self.n, self, Up, self.cost + 1)

proc moveDown(self: PuzzleState): PuzzleState =
   if self.blankRow == self.n - 1:
      result = nil
   else:
      let blankIndex = self.blankRow * self.n + self.blankCol
      let target = blankIndex + self.n
      var newBoard = self.board
      swap(newBoard[blankIndex], newBoard[target])
      result = newPuzzleState(newBoard, self.n, self, Down, self.cost + 1)

proc expand(self: PuzzleState) =
   ## expand the node
   # add child nodes in order of UDLR
   if len(self.children) == 0:
      let upChild = self.moveUp()
      if upChild != nil:
         self.children.add(upChild)
      let downChild = self.moveDown()
      if downChild != nil:
         self.children.add(downChild)
      let leftChild = self.moveLeft()
      if leftChild != nil:
         self.children.add(leftChild)
      let rightChild = self.moveRight()
      if rightChild != nil:
         self.children.add(rightChild)

proc writeOutput(path: seq[PuzzleAction], cost, nodes, depth, maxDepth: int, runningTime, maxRam: float) =
   ## Function that Writes to output.txt
   var file: File
   var succ = false
   try:
      file = open("output.txt", fmWrite)
      succ = true
      file.write(&"path_to_goal: {path}\n")
      file.write(&"cost_of_path: {cost}\n")
      file.write(&"nodes_expanded: {nodes}\n")
      file.write(&"search_depth: {depth}\n")
      file.write(&"max_search_depth: {maxDepth}\n")
      file.write(&"running_time: {runningTime:.8}\n")
      file.write(&"max_ram_usage: {maxRam:.8}\n")
   finally:
      if succ: close(file)

proc calculateTotalCost(state: PuzzleState): int =
   ## calculate the total estimated cost of a state
   discard

proc calculateManhattanDist(idx, value, n: int): int =
   ## calculatet the manhattan distance of a tile
   discard

proc testGoal(state: PuzzleState): bool =
   ## test the state is the goal state or not
   var solvedConf: seq[int]
   for i in 0 ..< state.n * state.n:
      solvedConf.add i   
   hash(state) == hash(solvedConf)

proc bfsSearch(initialState: PuzzleState): (PuzzleState, int, int) =
   ## BFS search
   var frontier = initDeque[PuzzleState]()
   frontier.addLast(initialState)
   var discovered = initSet[PuzzleState]()
   discovered.incl(initialState)
   var maxDepth = 0
   var nodesExpanded = 0
   while frontier.len > 0:
      let state = frontier.popFirst()
      if testGoal(state):
         return (state, nodesExpanded, maxDepth)
      state.expand()
      nodesExpanded.inc
      for neighbor in childrenOf(state):
         if neighbor.cost > maxDepth:
            maxDepth = neighbor.cost
         if neighbor notin discovered:
            frontier.addLast(neighbor)
            discovered.incl(neighbor)
   result = (nil, nodesExpanded, maxDepth)

proc bfsSearch2(initialState: PuzzleState): (PuzzleState, int, int) =
   ## BFS search
   var maxDepth = 0
   var nodesExpanded = 0
   var frontier = initDeque[PuzzleState]()
   frontier.addLast(initialState)
   var exploredUfrontier = initSet[PuzzleState]()
   exploredUfrontier.incl(initialState)
   while frontier.len > 0:
      let state = frontier.popFirst()
      exploredUfrontier.incl(state)
      if testGoal(state):
         return (state, nodesExpanded, maxDepth)
      state.expand()
      nodesExpanded.inc
      for neighbor in childrenOf(state):
         if neighbor.cost > maxDepth:
            maxDepth = neighbor.cost
         if neighbor notin exploredUfrontier:
            frontier.addLast(neighbor)
            exploredUfrontier.incl(neighbor)
   result = (nil, nodesExpanded, maxDepth)

proc dfsSearch(initialState: PuzzleState): (PuzzleState, int, int) =
   ## DFS search
   var frontier = newSeq[PuzzleState]()
   frontier.add(initialState)
   var discovered = initSet[PuzzleState]()
   discovered.incl(initialState)
   var maxDepth = 0
   var nodesExpanded = 0
   while frontier.len > 0:
      let state = frontier.pop()
      if testGoal(state):
         return (state, nodesExpanded, maxDepth)
      state.expand()
      nodesExpanded.inc
      for neighbor in childrenOf(state):
         if neighbor.cost > maxDepth:
            maxDepth = neighbor.cost
         if neighbor notin discovered:
            frontier.add(neighbor)
            discovered.incl(neighbor)
   result = (nil, nodesExpanded, maxDepth)

proc dlsSearch(initialState: PuzzleState; limit = 50): (PuzzleState, int, int) =
   ## DLS search
   var frontier = newSeq[PuzzleState]()
   frontier.add(initialState)
   var discovered = initSet[PuzzleState]()
   var maxDepth = 0
   var nodesExpanded = 0
   while frontier.len > 0:
      let state = frontier.pop()
      if testGoal(state):
         return (state, nodesExpanded, maxDepth)
      if state.cost <= limit:
         state.expand()
         nodesExpanded.inc
         for neighbor in childrenOf(state):
            if neighbor.cost > maxDepth:
               maxDepth = neighbor.cost
            if neighbor notin discovered:
               discovered.incl(neighbor)
               frontier.add(neighbor)
   result = (nil, nodesExpanded, maxDepth)

proc idsSearch(initialState: PuzzleState; maxLimit = 50): (PuzzleState, int, int) =
   ## IDS search
   var maxDepth = 0
   var nodesExpanded = 0
   for i in 1 .. maxLimit:
      let (finalState, tNodesExpanded, tMaxDepth) = dlsSearch(initialState, i)
      nodesExpanded += tNodesExpanded
      if tMaxDepth > maxDepth:
         maxDepth = tMaxDepth
      if finalState != nil:
         return (finalState, nodesExpanded, maxDepth)
   result = (nil, nodesExpanded, maxDepth)

proc ucsSearch(initialState: PuzzleState): (PuzzleState, int, int) =
   ## UCS search
   var frontier = newHeapQueue[PuzzleState]()
   frontier.push(initialState)
   var discovered = initSet[PuzzleState]()
   discovered.incl(initialState)
   var maxDepth = 0
   var nodesExpanded = 0
   while frontier.len > 0:
      let state = frontier.pop()
      if testGoal(state):
         return (state, nodesExpanded, maxDepth)
      state.expand()
      nodesExpanded.inc
      for neighbor in childrenOf(state):
         if neighbor.cost > maxDepth:
            maxDepth = neighbor.cost
         if neighbor notin discovered:
            frontier.push(neighbor)
            discovered.incl(neighbor)
   result = (nil, nodesExpanded, maxDepth)

proc aStarSearch(initialState: PuzzleState): (PuzzleState, int, int) =
   ## A* search
   discard

proc main() =
   # Main Function that reads in Input and Runs corresponding Algorithm
   let sm = paramStr(1).toLowerAscii()
   var beginState = newSeq[int]()
   for num in paramStr(2).split(","):
      beginState.add parseInt(num)
   let size = sqrt(beginState.len.float).int
   let startTime = epochTime()
   let hardState = newPuzzleState(beginState, size)
   let (finalState, nodesExpanded, maxDepth) = 
      if sm == "bfs":
         bfsSearch2(hardState)
      elif sm == "dfs":
         dfsSearch(hardState)
      elif sm == "dls":
         dlsSearch(hardState)
      elif sm == "ids":
         idsSearch(hardState)
      elif sm == "ucs":
         ucsSearch(hardState)
      elif sm == "ast":
         aStarSearch(hardState)
      else:
         quit("Enter valid command arguments!")
   let runningTime = epochTime() - startTime
   let ram = getOccupiedMem() / 1024
   if finalState != nil:
      let depthAndCost = finalState.cost
      let path = finalState.getSolution()
      writeOutput(path, depthAndCost, nodesExpanded, depthAndCost, maxDepth, runningTime, ram)
   else:
      quit("Failed to find solution!")

main()
