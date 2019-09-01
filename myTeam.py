# myTeam.py
# ---------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
#
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).



from captureAgents import CaptureAgent
import random, time, util, math
from game import Directions, Actions
import game
import distanceCalculator


#################
# Team creation #
#################


def createTeam(firstIndex, secondIndex, isRed,
			   first='OffensiveAgent', second='DefensiveAgent'):
	"""
	This function should return a list of two agents that will form the
	team, initialized using firstIndex and secondIndex as their agent
	index numbers.  isRed is True if the red team is being created, and
	will be False if the blue team is being created.

	As a potentially helpful development aid, this function can take
	additional string-valued keyword arguments ("first" and "second" are
	such arguments in the case of this function), which will come from
	the --redOpts and --blueOpts command-line arguments to capture.py.
	For the nightly contest, however, your team will be created without
	any extra arguments, so you should make sure that the default
	behavior is what you want for the nightly contest.
	"""

	# The following line is an example only; feel free to change it.
	return [eval(first)(firstIndex), eval(second)(secondIndex)]


##########
# Agents #
##########

# This is the main agent class we used for both agents
class AggressiveAgent(CaptureAgent):

	# This method initailize the all usefull global variables for each agent
	def registerInitialState(self, gameState):
		CaptureAgent.registerInitialState(self, gameState)
		# start point
		self.sanctuary = gameState.getAgentPosition(self.index)
		self.isRed = gameState.isOnRedTeam(self.index)
		self.width = gameState.data.layout.width
		self.height = gameState.data.layout.height
		if self.isRed:
			self.left = 0
			self.right = self.width / 2
			self.food_left = self.width / 2
			self.food_right = self.width
		else:
			self.left = self.width / 2
			self.right = self.width
			self.food_left = 0
			self.food_right = self.width / 2
		# All accessible point at the edge of our side to other side
		self.portals = self.getPortals(gameState)
		self.myside = self.getMyside(gameState)
		self.walls = gameState.getWalls()
		self.remainFood = self.getFood(gameState).asList()
		self.myFood = self.getFoodYouAreDefending(gameState).asList()

		self.oppoCaps = self.getCapsules(gameState)
		self.myCaps = self.getCapsulesYouAreDefending(gameState)
		self.opponents = self.getOpponents(gameState)
		self.myTeammate = self.getTeam(gameState)[1]
		# A dictionary to store a cost between two position (deadend to a chowk point)
		self.depth = self.getDepthFromMap(gameState)
		# if not self.isRed:
		# 	self.depth = self.reverseDepth()
		self.loop = 30
		# steps of simulation
		self.step = 50
		self.nodes = util.Counter()
		# reward from every simulation (allow dynamic chaning)
		self.reward = 0
		self.i = 0
		# store the action along with
		self.path = []
		self.pathIndex = 0
		# exploration rate
		self.cp = 0.5
		self.ccc = 0
		self.visitedPos = set()
		self.loop_count = 1
		# main concept that determine whether the food is safe to get or not
		self.mySafeFood = list()
		# teammate safefood
		self.teamMateSafeFood = list()
		self.agentPos = dict()
		self.agentState = dict()
		self.oppoGhosts = list()
		self.oppoActGhosts = list()
		self.oppoScareTimer = dict()
		self.oppoPacSeen = list()
		self.oppoPacGuess = list()
		self.oppoPacPos = list()
		self.numOppoPac = 0
		self.lastSeen = list()
		# 
		self.effective = 0
		


		
	# this method only run one time at the start of the game when initialize
	# the depth 
	# This method return a dictionary
	def getDepthFromMap(self, gameState):
		depth = dict()
		visited = set()
		visited.add(self.sanctuary)
		q = util.Queue()
		q.push(self.sanctuary)
		while not q.isEmpty():
			current_Position = q.pop()
			for neighbor in Actions.getLegalNeighbors(current_Position, self.walls):
				if neighbor not in visited:
					visited.add(neighbor)
					q.push(neighbor)
					if neighbor[0] in range(self.food_left, self.food_right):
						direction = neighbor
						if self.isDeadEnd(current_Position, direction):  
							depth[current_Position] = (1, current_Position)
							depth[direction] = (2, current_Position)
							q_ = util.Queue()
							q_.push(direction)
							while not q_.isEmpty():
								ele = q_.pop()
								for next in Actions.getLegalNeighbors(ele, self.walls):
									if next not in depth:
										depth[next] = (
											self.getMazeDistance(next, current_Position) + 1, current_Position)
										visited.add(next)
										q_.push(next)
							continue
		return depth
	
	def reverseDepth(self):
		newDepth = dict()
		for dep in self.depth:
			cost, chowkPoint = dep
			newDepth[chowkPoint] = (cost,dep)
		return newDepth

	# This is a helper function to test if it can come back to our side if
	# the chowk point is blocked
	# return true if it have nowhere to go return false if reach one of the 
	# portals
	def isDeadEnd(self, block, checkPoint):
		target = self.sanctuary
		Q = util.PriorityQueue()
		Q.push(checkPoint, 1)
		visited = [block, checkPoint]
		while not Q.isEmpty():
			curPos = Q.pop()
			neighbors = Actions.getLegalNeighbors(curPos, self.walls)
			for neighbor in neighbors:
				if neighbor not in visited:
					x, _ = neighbor
					if (self.isRed and x <= self.right) or (not self.isRed and x >= self.left):
						return False
					visited.append(neighbor)
					priority = self.getMazeDistance(neighbor, target)
					Q.push(neighbor, priority)
		return True

	# this method will return all position that is on edge of our side which 
	# can cross from one side to another side
	def getPortals(self, gameState):

		portals = list()

		if self.isRed:
			oppoMid = self.right
			middle = oppoMid -1
		else:
			
			middle = self.left
			oppoMid = middle - 1
		for y in range(self.height):
			if not gameState.hasWall(middle, y) and not gameState.hasWall(oppoMid, y):
				portals.append((middle,y))

		return sorted(portals, key=lambda s: s[1])

	def getMyside(self, gameState):
		pos = list()
		for i in range(self.left, self.right):
			for j in range(self.height):
				if not gameState.hasWall(i,j):
					pos.append((i,j))
		return pos

	# This method return the closest target from the list of targets
	# if both agents are offensive alter the distance which allow them 
	# to choose different targets
	def getTarget(self, targets, bothAttack=True):
		minDist = self.height * self.width
		minTarget = None
		for target in targets:
			dist = self.getMazeDistance(target, self.agentPos[self.index])
			if bothAttack:
				if self.isOffensive:
					dist += self.height-target[1]
					
				else:
					dist += target[1]
					
			if dist <minDist:
				minDist = dist
				minTarget = target
		return minTarget

	# This method store the position that food disappeared
	def guessoppoPacGuess(self, gameState):
		self.oppoPacGuess = list()
		preFoodPos = self.myFood + self.myCaps
		self.myCaps = self.getCapsulesYouAreDefending(gameState)
		self.myFood = self.getFoodYouAreDefending(gameState).asList()
		FoodPos = self.myFood + self.myCaps
		for food in preFoodPos:
			if food not in FoodPos:
				self.oppoPacGuess.append(food)

	# return number of pacman on our side
	def numPacOnMySide(self):
		num = 0
		for i in self.opponents:
			if self.agentState[i].isPacman:
				num += 1
		return num

	# the generate a new state; update all usefull info
	def updateGameState(self, gameState):
		self.oppoPacSeen = []
		self.oppoGhosts = []
		self.oppoCaps = self.getCapsules(gameState)
		number = gameState.data.timeleft / 4
		self.remainFood = self.getFood(gameState).asList()
		self.oppoActGhosts = []

		for agent in range(gameState.getNumAgents()):
			self.agentState[agent] = gameState.getAgentState(agent)
			self.agentPos[agent] = gameState.getAgentPosition(agent)
			self.oppoScareTimer[agent] = self.agentState[agent].scaredTimer
			if agent in self.opponents:
				if not self.agentPos[agent] is None:
					if self.agentState[agent].isPacman:
						self.oppoPacSeen += [agent]
					else:
						self.oppoGhosts += [agent]
						if self.agentState[agent].scaredTimer <= 2:
							self.oppoActGhosts += [agent]

		self.guessoppoPacGuess(gameState)
		self.oppoPacPos = self.oppoPacGuess
		for oppoPac in self.oppoPacSeen:
			if self.agentPos[oppoPac] not in self.oppoPacPos:
				self.oppoPacPos += [self.agentPos[oppoPac]]
		if len(self.oppoPacPos) == 0:
			if self.effective > 0:
				self.effective = self.effective - 1
		if len(self.oppoPacPos) > 0:
			self.effective = 5
			self.lastSeen = self.oppoPacPos

		self.teamMateSafeFood = self.getSafeFood(self.myTeammate)
		self.mySafeFood = self.getSafeFood(self.index)
		self.numOppoPac = self.numPacOnMySide()

	# This is the mean concept which calculated using depth
	# plus and minus the cost of myself and ghost accordingly if find in depth
	def getSafeFood(self, index):
		safeFood = list()
		targets = list(self.remainFood)
		targets += self.oppoCaps
		for food in targets:
			minChaserCost = self.height * self.width
			chaser = None
			myCost = self.getMazeDistance(self.agentPos[index], food)
			for ghost in self.oppoGhosts:
				dist = self.getMazeDistance(self.agentPos[ghost], food)
				if dist < minChaserCost:
					minChaserCost = dist
					chaser = ghost
			if food in self.depth:
				cost, chowkPoint = self.depth[food]
				myCost += cost
				minChaserCost -= cost
			if myCost < minChaserCost or myCost < self.oppoScareTimer[chaser] - 1:
				safeFood.append(food)
		return safeFood

	# this method return the position that have the lowest cost to all points
	# the position will be closer to caps
	def getBestPos(self):
		targets = self.myFood + self.myCaps
		minDist = self.height * self.width
		bestPos = None
		if self.effective > 0:
			for ghost in self.lastSeen:
				dist = self.getMazeDistance(ghost, self.agentPos[self.index]) * 0.78
				if dist < minDist:
					minDist = dist
					bestPos = ghost
		for i in range(self.left, self.right):
			for j in range(self.height):
				if not self.walls[i][j]:
					sumDist = 0
					for tar in self.myFood:
						sumDist += self.getMazeDistance((i, j), tar) * 0.78
					for caps in self.myCaps:
						sumDist += self.getMazeDistance((i, j), caps) * 0.22
					if sumDist < minDist:
						minDist = sumDist
						bestPos = (i, j)
		if bestPos is None:
			return self.portals[len(self.portals) / 2]
		return bestPos

	# this method is to pick the defense position 
	def pickDefenseTarget(self):
		enemyInMySight = list()
		for i in self.opponents:
			if self.agentPos[i] is not None and self.agentState[i].isPacman:
				enemyInMySight.append(self.agentPos[i])
		for p in self.oppoPacGuess:
			if p not in enemyInMySight:
				enemyInMySight.append(p)

		if len(enemyInMySight) > 0 and self.agentState[self.index].scaredTimer <= 0:
			return self.getTarget(enemyInMySight, False)
		target = self.getTarget(self.mySafeFood, False)
		if target is None:
			return self.getBestPos()
		return target

	# main method that make the decision to attack or defense based on safefood
	# return two booleans which the firt is current agent decision, the second is
	# teammate decision. return true if is offensive
	def getDecision(self, gameState):

		aOffense = False
		bOffense = False
		if len(self.remainFood) <= 2:
			return False, False
		self.mySafeFood += self.oppoCaps
		self.teamMateSafeFood += self.oppoCaps
		aOffense = len(self.mySafeFood) >= 0
		bOffense = len(self.teamMateSafeFood) >= 0
		if not self.isOffensive:
			aOffense, bOffense = bOffense, aOffense
		if aOffense and bOffense:
			if 5 < len(self.remainFood):
				return True, True
			if self.agentState[self.index].scaredTimer <= 0:
				if self.agentState[self.myTeammate].scaredTimer <= 0:
					myDist = 0
					mateDist = 0
					for food in self.remainFood:
						myDist += self.getMazeDistance(self.agentPos[self.index], food)
						mateDist += self.getMazeDistance(self.agentPos[self.myTeammate], food)
					if myDist < mateDist:
						return True, False
					else:
						return False, True
					myDist = self.getMazeDistance(self.agentPos[self.index], self.sanctuary)
					teamMateDist = self.getMazeDistance(self.agentPos[self.myTeammate], self.sanctuary)
					if myDist < 10:
						aOffense = True
					if teamMateDist < 10:
						bOffense = True
					else:
						bOffense = True
			else:
				if self.agentState[self.myTeammate].scaredTimer <= 0:
					aOffense = True
				else:
					return True, True

		return aOffense, bOffense

	# return the position to block enemy from entering
	def preventOppo(self, ghostPos):
		minDist = self.height * self.width
		minPos = None
		for pot in self.portals:
			dist = self.getMazeDistance(ghostPos, pot)
			if dist < minDist:
				minDist = dist
				minPos = pot
		return minPos

	# this method is main logic for each step's decision
	# 1. update new gameState
	# 2. getDecision for both agents
	# 3. do somthing based on the decision
	# 4. use A* to return an action
	def chooseAction(self, gameState):
		self.updateGameState(gameState)
		myDec, myTeamMateDec = self.getDecision(gameState)
		if myDec:
			targets = list()
			if self.remainFood > 2:
				targets = list(self.mySafeFood)
			if self.agentState[self.index].numCarrying > 1:
				targets += self.portals
			target = self.getTarget(targets, myTeamMateDec)
			# target = self.uct(gameState)

		else:
			if self.agentState[self.index].numCarrying > 0:
				target = self.getTarget(self.portals, False)
			else:
				if myTeamMateDec:
					if self.numOppoPac == 0:
						if len(self.oppoGhosts) != 0:
							target = self.preventOppo(self.agentPos[self.oppoGhosts[0]])
						else:
							target = self.portals[len(self.portals) / 2]
					else:
						target = self.pickDefenseTarget()
				else:
					numOfGhostSeen = len(self.oppoGhosts)
					if self.numOppoPac == 0:
						if self.isOffensive:
							if numOfGhostSeen == 0:
								target = self.portals[len(self.portals) / 3]
							elif numOfGhostSeen == 1:
								target = self.portals[len(self.portals) / 3]
							else:
								target = self.preventOppo(self.agentPos[self.oppoGhosts[0]])
						else:
							if numOfGhostSeen == 0:
								target = self.portals[len(self.portals) * 2 / 3 - 1]
							elif numOfGhostSeen == 1:
								target = self.pickDefenseTarget()
							else:
								target = self.preventOppo(self.agentPos[self.oppoGhosts[1]])
					elif self.numOppoPac == 1:
						if self.isOffensive:
							if len(self.oppoGhosts)!=0:
								target = self.preventOppo(self.agentPos[self.oppoGhosts[0]])
							else:
								target = self.pickDefenseTarget()
						else:
							target = self.pickDefenseTarget()
					else:
						target = self.pickDefenseTarget()

		if target is None:
			target = self.getBestPos()
		
		return self.getPath(target, gameState)

	# method to return the best action
	# implement as a online apporach for A*
	def getPath(self,target, gameState):
		path = self.aStarSearch(gameState, target)

		if len(path) == 0:
			actions = gameState.getLegalActions(self.index)

			minDist = self.height*self.width
			minGhost = None
			for ghost in self.oppoGhosts:
				dist = self.getMazeDistance(self.agentPos[ghost],self.agentPos[self.index])
				if dist < minDist:
					minDist = dist
					minGhost = ghost

			for action in actions:
				direction_vector = Actions.directionToVector(action)
				successor_Coordinate = (
					int(self.agentPos[self.index][0] + direction_vector[0]), int(self.agentPos[self.index][1] + direction_vector[1]))

				if minGhost is not None:
					if self.getMazeDistance(successor_Coordinate ,self.agentPos[minGhost]) > minDist:
						return action
				else:
					return random.sample(actions,1)[0]
			return Directions.STOP
		return path[0]

	def getSuccessor(self, gameState, action):
		"""
		Finds the next successor which is a grid position (location tuple).
		"""
		successor = gameState.generateSuccessor(self.index, action)
		pos = successor.getAgentState(self.index).getPosition()
		if pos != util.nearestPoint(pos):
			# Only half a grid position was covered
			return successor.generateSuccessor(self.index, action)
		else:
			return successor

	def getOppoPacPos(self):
		oppoPac = list()
		for i in self.opponents:
			if self.agentPos[i] is not None and self.agentState[i].isPacman and self.agentState[i].scaredTimer <= 0:
				oppoPac.append(self.agentPos[i])
		return oppoPac

	# this method will return a plan using A*
	# the plan will take the opponent position into account
	def aStarSearch(self, gameState, target):
		myPosition = self.agentPos[self.index]
		if myPosition == target:
			return []

		opponentGhostPositions = set()
		for ghost in self.oppoActGhosts:
			opponentGhostPositions.add(self.agentPos[ghost])
		if not self.getMazeDistance(self.agentPos[self.index], target) < 2 and not target in self.getOppoPacPos():
			for ghost in opponentGhostPositions:
				opponentGhostPositions = opponentGhostPositions | set(Actions.getLegalNeighbors(ghost, self.walls))

		q = util.PriorityQueue()
		q.push((gameState, myPosition, []), util.manhattanDistance(myPosition, target))
		visited = set()
		visited.add(myPosition)
		while not q.isEmpty():
			currentState, currentPosition, path = q.pop()
			if currentPosition == target:
				return path
			else:
				for action in currentState.getLegalActions(self.index):
					successor = self.getSuccessor(currentState, action)
					direction_vector = Actions.directionToVector(action)
					successor_Coordinate = (
					int(currentPosition[0] + direction_vector[0]), int(currentPosition[1] + direction_vector[1]))
					if successor_Coordinate not in visited:
						if successor_Coordinate not in opponentGhostPositions:
							priority = util.manhattanDistance(target, successor_Coordinate) + len(path + [action])
							q.push((successor, successor_Coordinate, path + [action]), priority)
							if not target == successor_Coordinate:
								visited.add(successor_Coordinate)
						else:
							continue
		return []

	# this is the UCT methord which outputs an action with the maximum UCB value
	# it calls mct function in a range
	def uct(self, gameState):
		self.i += 1
		if self.i == self.loop:
			return
		currentPos = gameState.getAgentState(self.index).getPosition()
		actions = util.Counter()
		# recursively go through UCT
		self.loop_count = 0
		for i in range(0, self.loop):
			self.path = []
			self.pathIndex = 0
			self.mct_if_count = 1
			self.mct_else_count = 1
			self.mct(gameState, currentPos)
			self.loop_count += 1

		# get the no go back or stop actions
		actionValid = self.actionNoStop(gameState)
		currentDir = gameState.getAgentState(self.index).configuration.direction
		reversedDir = Directions.REVERSE[currentDir]
		if reversedDir in actionValid and len(actionValid) > 1:
			actionValid.remove(reversedDir)

		# select the action with highest USB value
		for i in actionValid:
			nextPos = self.moveTo(gameState, i)
			actions[i] = self.nodes[nextPos][4]
		nextStep = self.moveTo(gameState, actions.argMax())
		return nextStep

	# get the position after next move
	def moveTo(self, gameState, action):
		nextState = self.getSuccessor(gameState, action)
		nextPos = nextState.getAgentState(self.index).getPosition()
		return nextPos

	# get all the avaliable actions without "stop"
	def actionNoStop(self, gameState):
		actionValid = gameState.getLegalActions(self.index)
		actionValid.remove('Stop')
		return actionValid

	
	# calculate the UCB on this node
	def calculateUCB(self, currentPos):

		parents = self.nodes[currentPos][1]
		ns = self.nodes[parents][3]
		nsa = self.nodes[currentPos][3]
		nodesReward = self.nodes[currentPos][2]
		inside = 2 * math.log(ns) / nsa
		return (nodesReward + self.cp * math.sqrt(inside))

	# this method is doing all the iteration and calculation(UCB)
	# steps of simulation
	def mct(self, gameState, currentPos):

		if currentPos not in self.nodes.keys() or \
				self.nodes[currentPos][5] == 1:
			self.nodes[currentPos] = [1, currentPos, 1, 1, 1, 1]
			self.nodes[currentPos][0] = currentPos
			self.path.append(currentPos)
			self.pathIndex += 1
			actValid = self.actionNoStop(gameState)
			currentDir = gameState.getAgentState(self.index).configuration.direction
			reversedDir = Directions.REVERSE[currentDir]
			if reversedDir in actValid and len(actValid) > 1:
				actValid.remove(reversedDir)
			# initialize value the child nodes and its child nods
			# store format: [currentPos, parentPos,nodeReward, visits, UCB]
			self.nodes[currentPos][5] = actValid

			for act in actValid:
				self.nodes[self.moveTo(gameState, act)] = [1, currentPos, 2000, 1, 2000, 1]  # initial "infinite" value

			# just pick the first avaliable
			actPick = actValid[0]
			# follow this action
			actPickState = self.getSuccessor(gameState, actPick)
			actPickPos = actPickState.getAgentState(self.index).getPosition()
			nodeReward = self.randomSimulation(self.step, actPickState)

			self.nodes[actPickPos][2] = nodeReward
			self.nodes[actPickPos][3] += 1
			self.nodes[actPickPos][4] = self.calculateUCB(actPickPos)
			self.reward = nodeReward
			self.path.append(actPickPos)
			self.pathIndex += 1
			self.backprop(actPickPos)
			return
		else:
			self.path.append(currentPos)
			self.pathIndex += 1

			actions = util.Counter()
			actValid = self.nodes[currentPos][5]

			# put avaliable actions into the dict actions, in order to get max-arg of it
			for i in actValid:
				nextPos = self.moveTo(gameState, i)
				actions[i] = self.nodes[nextPos][4]

			nextStep = self.moveTo(gameState, actions.argMax())
			actPickState = self.getSuccessor(gameState, actions.argMax())
			self.mct_else_count += 1
			self.mct(actPickState, nextStep)

	# given positions now and then, outputs the action conducted
	def tellMove(self, nextPos, currentPos):
		difference = ((nextPos[0] - currentPos[0]), (nextPos[1] - currentPos[1]))
		if difference == (1, 0):
			return "East"
		elif difference == (0, 1):
			return "North"
		elif difference == (-1, 0):
			return "West"
		elif difference == (0, -1):
			return "South"
		else:
			return -1

	# this method does the backpropagation
	def backprop(self, currentPos):
		self.pathIndex -= 1
		parentPos = self.path[self.pathIndex]
		self.nodes[parentPos][2] += self.reward
		self.nodes[parentPos][3] += 1
		self.nodes[parentPos][4] = self.calculateUCB(parentPos)
		if currentPos == parentPos:
			return
		else:
			self.backprop(parentPos)

	# this does the simulation part, return a reward
	def randomSimulation(self, steps, gameState):
		score = 0
		stateNext = gameState
		foodList = self.mySafeFood
		while steps > 0:
			actions = self.actionNoStop(stateNext)
			currentDir = stateNext.getAgentState(self.index).configuration.direction
			reversedDir = Directions.REVERSE[currentDir]
			if reversedDir in actions and len(actions) > 1:
				actions.remove(reversedDir)

			# Randomly chooses a valid action
			a = random.choice(actions)

			# Compute new state and update steps
			stateNext = stateNext.generateSuccessor(self.index, a)
			steps -= 1

			if stateNext.getAgentState(self.index).getPosition() in self.path:
				score -= 2
			if stateNext.getAgentState(self.index).getPosition() in foodList:
				score += 150
				return score
		return score

# offensive tendency agent
class OffensiveAgent(AggressiveAgent):
	def registerInitialState(self, gameState):
		AggressiveAgent.registerInitialState(self, gameState)
		self.isOffensive = True

# deffensive tendency agent
class DefensiveAgent(AggressiveAgent):
	def registerInitialState(self, gameState):
		AggressiveAgent.registerInitialState(self, gameState)
		self.isOffensive = False
		
