from collections import deque
import random
import math
import time
import pygame as pg
import pickle
import neat

SCREEN_SIZE = (1280, 720)
FPS = 60
SCALE = 0.5
ROAD_WIDTH = int(280 * SCALE)
BROKEN_LINE_WIDTH = int(12 * SCALE)
BROKEN_LINE_LENGTH = int(30 * SCALE)
CAR_SPEED = int(8 * SCALE)
CIRCLE_RAD = int(25 * SCALE)
OPTIMAL_DISTANCE = math.sqrt(2 * CIRCLE_RAD ** 2) - CIRCLE_RAD // 2
GREEN = (0, 255, 0)
YELLOW = (255, 255, 0)
RED = (255, 0, 0)
TRAFFIC_LIGHT_COLORS = [GREEN, YELLOW, RED]
TRAFFIC_LIGHT_WIDTH = int(20 * SCALE)
YELLOW_TIME = 0.5
SPAWNRATE = 5  # cars per second


def distance(p1, p2):
    return math.sqrt((p1[0] - p2[0]) ** 2 + (p1[1] - p2[1]) ** 2)


class Crossroad:
    def __init__(self):
        self.id = 0
        self.timer = 0
        self.averageTime = 0
        self.maxWaitingTime = 0
        self.sumWaitingTime = 0
        self.prevCarID = 0
        self.carsOnRoads = 0
        self.processedCars = 0
        self.sumWaitingTimeOfProcessedCars = 0
        self.road1 = Road(1, 'vertical')
        self.road2 = Road(2, 'horizontal')
        self.roads = [self.road1, self.road2]
        self.road1.lines.append(Line(1, SCREEN_SIZE[0] // 2 - ROAD_WIDTH // 4 - ROAD_WIDTH // 8, (0, 1)))
        self.road1.lines.append(Line(2, SCREEN_SIZE[0] // 2 - ROAD_WIDTH // 4 + ROAD_WIDTH // 8, (0, 1)))
        self.road1.lines.append(Line(3, SCREEN_SIZE[0] // 2 + ROAD_WIDTH // 4 - ROAD_WIDTH // 8, (0, -1)))
        self.road1.lines.append(Line(4, SCREEN_SIZE[0] // 2 + ROAD_WIDTH // 4 + ROAD_WIDTH // 8, (0, -1)))

        self.road2.lines.append(Line(1, SCREEN_SIZE[1] // 2 - ROAD_WIDTH // 4 - ROAD_WIDTH // 8, (-1, 0)))
        self.road2.lines.append(Line(2, SCREEN_SIZE[1] // 2 - ROAD_WIDTH // 4 + ROAD_WIDTH // 8, (-1, 0)))
        self.road2.lines.append(Line(3, SCREEN_SIZE[1] // 2 + ROAD_WIDTH // 4 - ROAD_WIDTH // 8, (1, 0)))
        self.road2.lines.append(Line(4, SCREEN_SIZE[1] // 2 + ROAD_WIDTH // 4 + ROAD_WIDTH // 8, (1, 0)))

        self.crossroadRect = pg.Rect(SCREEN_SIZE[0] // 2 - ROAD_WIDTH // 2, SCREEN_SIZE[1] // 2 - ROAD_WIDTH // 2,
                                     ROAD_WIDTH, ROAD_WIDTH)
        self.isSwitched = True
        self.trafficLightsState = {1: {1: 0, 2: 0, 3: 0, 4: 0}, 2: {1: 2, 2: 2, 3: 2, 4: 2}}
        self.switcher(self.trafficLightsState)

        self.road1.lines[2].possibleDirections = [(2, 2)]
        self.road1.lines[3].possibleDirections = [(2, 4)]

        self.road2.lines[0].possibleDirections = [(2, 1)]
        self.road2.lines[1].possibleDirections = ((2, 2), (1, 2))
        self.road2.lines[2].possibleDirections = [(2, 3)]
        self.road2.lines[3].possibleDirections = ((2, 4), (1, 1))

        for road in self.roads:
            for line in road.lines:
                if line.direction == (0, -1):
                    line.trafficLightRect = pg.Rect(line.coordinate - ROAD_WIDTH // 8,
                                                    self.crossroadRect.bottom,
                                                    ROAD_WIDTH // 4, TRAFFIC_LIGHT_WIDTH)
                elif line.direction == (0, 1):
                    line.trafficLightRect = pg.Rect(line.coordinate - ROAD_WIDTH // 8,
                                                    self.crossroadRect.top - TRAFFIC_LIGHT_WIDTH,
                                                    ROAD_WIDTH // 4, TRAFFIC_LIGHT_WIDTH)
                elif line.direction == (1, 0):
                    line.trafficLightRect = pg.Rect(self.crossroadRect.left - TRAFFIC_LIGHT_WIDTH,
                                                    line.coordinate - ROAD_WIDTH // 8,
                                                    TRAFFIC_LIGHT_WIDTH, ROAD_WIDTH // 4)
                elif line.direction == (-1, 0):
                    line.trafficLightRect = pg.Rect(self.crossroadRect.right,
                                                    line.coordinate - ROAD_WIDTH // 8,
                                                    TRAFFIC_LIGHT_WIDTH, ROAD_WIDTH // 4)

        # (roadNumber, line, destinationLine)
        self.possibleRoutesWithTurns = [(1, 3, 2), (1, 4, 4), (2, 2, 2), (2, 4, 3)]

    def trafficLightManager(self):
        self.timer += 1 / FPS
        if self.timer >= 10:
            self.timer = 0
            self.switcher({1: {1: 1, 2: 1, 3: 1, 4: 1}, 2: {1: 1, 2: 1, 3: 1, 4: 1}})
        elif self.trafficLightsState == {1: {1: 1, 2: 1, 3: 1, 4: 1}, 2: {1: 1, 2: 1, 3: 1, 4: 1}} \
                and self.timer >= YELLOW_TIME:
            self.timer = 0
            if self.isSwitched:
                self.switcher({1: {1: 2, 2: 2, 3: 2, 4: 2}, 2: {1: 0, 2: 0, 3: 0, 4: 0}})
            else:
                self.switcher({1: {1: 0, 2: 0, 3: 0, 4: 0}, 2: {1: 2, 2: 2, 3: 2, 4: 2}})
            self.isSwitched = not self.isSwitched

    def minDist(self, road_id, line1_id, line2_id):
        res = float("inf")
        for car in self.roads[road_id].lines[line1_id].carsOnLine:
            if not car.passed:
                if car.distToCrossroad < res:
                    res = car.distToCrossroad
        for car in self.roads[road_id].lines[line2_id].carsOnLine:
            if not car.passed:
                if car.distToCrossroad < res:
                    res = car.distToCrossroad
        return res

    def trafficLightManagerAI(self):
        self.timer += 1 / FPS
        c1 = len(self.road1.lines[0].queue) + len(self.road1.lines[1].queue)
        c2 = 0  # max waiting time
        for car in self.road1.lines[0].carsOnLine:
            if not car.passed:
                c1 += 1
                if car.waitingTime > c2:
                    c2 = car.waitingTime
        for car in self.road1.lines[1].carsOnLine:
            if not car.passed:
                c1 += 1
                if car.waitingTime > c2:
                    c2 = car.waitingTime
        c3 = self.minDist(0, 0, 1)

        c4 = len(self.road1.lines[2].queue) + len(self.road1.lines[3].queue)
        c5 = 0  # max waiting time
        for car in self.road1.lines[2].carsOnLine:
            if not car.passed:
                c4 += 1
                if car.waitingTime > c5:
                    c5 = car.waitingTime
        for car in self.road1.lines[3].carsOnLine:
            if not car.passed:
                c4 += 1
                if car.waitingTime > c5:
                    c5 = car.waitingTime
        c6 = self.minDist(0, 2, 3)

        c7 = len(self.road2.lines[0].queue) + len(self.road2.lines[1].queue)
        c8 = 0  # max waiting time
        for car in self.road2.lines[0].carsOnLine:
            if not car.passed:
                c7 += 1
                if car.waitingTime > c8:
                    c8 = car.waitingTime
        for car in self.road2.lines[1].carsOnLine:
            if not car.passed:
                c7 += 1
                if car.waitingTime > c8:
                    c8 = car.waitingTime
        c9 = self.minDist(1, 0, 1)

        c10 = len(self.road2.lines[2].queue) + len(self.road2.lines[3].queue)
        c11 = 0  # max waiting time
        for car in self.road2.lines[2].carsOnLine:
            if not car.passed:
                c10 += 1
                if car.waitingTime > c11:
                    c11 = car.waitingTime
        for car in self.road2.lines[3].carsOnLine:
            if not car.passed:
                c10 += 1
                if car.waitingTime > c11:
                    c11 = car.waitingTime
        c12 = self.minDist(1, 2, 3)

        c13 = CAR_SPEED
        c1, c2, c3 = c4, c5, c6
        output = nets[self.id].activate((c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13))
        if output[0] > 0:
            ge[self.id].fitness -= 0.1
            self.timer = 0
            self.switcher({1: {1: 1, 2: 1, 3: 1, 4: 1}, 2: {1: 1, 2: 1, 3: 1, 4: 1}})
        if self.trafficLightsState == {1: {1: 1, 2: 1, 3: 1, 4: 1}, 2: {1: 1, 2: 1, 3: 1, 4: 1}} \
                and self.timer >= YELLOW_TIME:
            self.timer = 0
            if self.isSwitched:
                self.switcher({1: {1: 2, 2: 2, 3: 2, 4: 2}, 2: {1: 0, 2: 0, 3: 0, 4: 0}})
            else:
                self.switcher({1: {1: 0, 2: 0, 3: 0, 4: 0}, 2: {1: 2, 2: 2, 3: 2, 4: 2}})
            self.isSwitched = not self.isSwitched

    def switcher(self, state):
        self.trafficLightsState = state
        for road in self.roads:
            for line in road.lines:
                line.trafficLightColor = state[road.number][line.number]

    def updateStatistics(self):
        self.averageTime = 0
        self.sumWaitingTime = 0
        self.carsOnRoads = 0
        for road in self.roads:
            for line in road.lines:
                for car in line.carsOnLine:
                    self.sumWaitingTime += car.waitingTime
                    if self.maxWaitingTime < car.waitingTime:
                        self.maxWaitingTime = car.waitingTime
                for car in line.queue:
                    self.sumWaitingTime += car.waitingTime

                self.carsOnRoads += len(line.carsOnLine) + len(line.queue)

        self.sumWaitingTime += self.sumWaitingTimeOfProcessedCars
        if self.carsOnRoads + self.processedCars > 0:
            self.averageTime = self.sumWaitingTime / (self.carsOnRoads + self.processedCars)
        else:
            self.averageTime = 0

    def addCar(self):
        new_car = Car()
        new_car.id = self.prevCarID + 1
        self.prevCarID = new_car.id
        # determining the point of dispatch
        new_car.road = random.choice(self.roads)
        new_car.line = random.choice(new_car.road.lines)

        while new_car.road.number == 1 and (new_car.line.number == 1 or new_car.line.number == 2):
            new_car.road = random.choice(self.roads)
            new_car.line = random.choice(new_car.road.lines)

        new_car.line.queue.append(new_car)

        new_car.destinationRoad = random.choice(self.roads)
        new_car.destinationLine = random.choice(new_car.destinationRoad.lines)
        while (new_car.destinationRoad.number, new_car.destinationLine.number) not in new_car.line.possibleDirections:
            new_car.destinationRoad = random.choice(self.roads)
            new_car.destinationLine = random.choice(new_car.destinationRoad.lines)

    def display(self, screen):
        pg.draw.rect(screen, (11, 218, 81), (0, 0, SCREEN_SIZE[0], SCREEN_SIZE[1]))

        pg.draw.rect(screen, (68, 68, 71), (SCREEN_SIZE[0] // 2 - ROAD_WIDTH // 2, 0, ROAD_WIDTH, SCREEN_SIZE[1]))
        y = 0
        while y < SCREEN_SIZE[1]:
            pg.draw.rect(screen, (255, 255, 255),
                         (SCREEN_SIZE[0] // 2 - ROAD_WIDTH // 4 - BROKEN_LINE_WIDTH // 2, y, BROKEN_LINE_WIDTH,
                          BROKEN_LINE_LENGTH))
            pg.draw.rect(screen, (255, 255, 255),
                         (SCREEN_SIZE[0] // 2 + ROAD_WIDTH // 4 - BROKEN_LINE_WIDTH // 2, y, BROKEN_LINE_WIDTH,
                          BROKEN_LINE_LENGTH))

            y += 2 * BROKEN_LINE_LENGTH

        pg.draw.rect(screen, (68, 68, 71), (0, SCREEN_SIZE[1] // 2 - ROAD_WIDTH // 2, SCREEN_SIZE[0], ROAD_WIDTH))
        x = 0
        while x < SCREEN_SIZE[0]:
            pg.draw.rect(screen, (255, 255, 255),
                         (x, SCREEN_SIZE[1] // 2 - ROAD_WIDTH // 4 - BROKEN_LINE_WIDTH // 2, BROKEN_LINE_LENGTH,
                          BROKEN_LINE_WIDTH))
            pg.draw.rect(screen, (255, 255, 255),
                         (x, SCREEN_SIZE[1] // 2 + ROAD_WIDTH // 4 - BROKEN_LINE_WIDTH // 2, BROKEN_LINE_LENGTH,
                          BROKEN_LINE_WIDTH))
            x += 2 * BROKEN_LINE_LENGTH

        for road in self.roads:
            for line in road.lines:
                pg.draw.rect(screen, TRAFFIC_LIGHT_COLORS[line.trafficLightColor], line.trafficLightRect)

        pg.draw.rect(screen, (255, 255, 255),
                     (SCREEN_SIZE[0] // 2 - BROKEN_LINE_WIDTH // 2, 0, BROKEN_LINE_WIDTH, SCREEN_SIZE[1]))
        pg.draw.rect(screen, (255, 255, 255),
                     (0, SCREEN_SIZE[1] // 2 - BROKEN_LINE_WIDTH // 2, SCREEN_SIZE[0], BROKEN_LINE_WIDTH))
        pg.draw.rect(screen, (68, 68, 71),
                     (SCREEN_SIZE[0] // 2 - ROAD_WIDTH // 2, SCREEN_SIZE[1] // 2 - ROAD_WIDTH // 2,
                      ROAD_WIDTH, ROAD_WIDTH))

        pg.draw.rect(screen, (11, 218, 81), (0, 0, SCREEN_SIZE[0], SCREEN_SIZE[1] // 2 - ROAD_WIDTH // 2))


class Road:
    def __init__(self, number, orientation):
        # lines = [(number, coordinate, direction)]
        self.lines = []
        self.orientation = orientation
        self.number = number


class Line:
    def __init__(self, number, coordinate, direction):
        self.number = number
        self.coordinate = coordinate
        self.direction = direction
        self.spawnPoint = None
        self.placeSpawnPoint()
        self.queue = deque()
        self.carsOnLine = []
        self.possibleDirections = None
        self.trafficLightRect = pg.Rect(0, 0, 0, 0)
        self.trafficLightColor = 2

    def deleteCar(self, car_id):
        index_to_delete = 0
        for i in range(len(self.carsOnLine)):
            if self.carsOnLine[i].id == car_id:
                index_to_delete = i
        self.carsOnLine.pop(index_to_delete)

    def placeSpawnPoint(self):
        if self.direction == (1, 0):
            self.spawnPoint = (-2 * CIRCLE_RAD, self.coordinate)
        elif self.direction == (-1, 0):
            self.spawnPoint = (SCREEN_SIZE[0] + 2 * CIRCLE_RAD, self.coordinate)
        elif self.direction == (0, 1):
            self.spawnPoint = (self.coordinate, -2 * CIRCLE_RAD)
        elif self.direction == (0, -1):
            self.spawnPoint = (self.coordinate, SCREEN_SIZE[1] + 2 * CIRCLE_RAD)

    def spawnCar(self):
        if self.queue:
            is_spawn_point_free = True
            for car in self.carsOnLine:
                if not car.passed and car.distToSpawnpoint < 2 * CIRCLE_RAD + OPTIMAL_DISTANCE:
                    is_spawn_point_free = False
            if is_spawn_point_free:
                car = self.queue.popleft()
                car.x = self.spawnPoint[0]
                car.y = self.spawnPoint[1]
                car.distToCrossroad = distance((car.x, car.y),
                                               (car.line.trafficLightRect.centerx, car.line.trafficLightRect.centery))
                self.carsOnLine.append(car)
            else:
                for car in self.queue:
                    car.wait()


class Car:
    def __init__(self):
        self.id = -1
        self.x = 0
        self.y = 0
        self.waitingTime = 0
        self.distToCrossroad = float("inf")
        self.distToSpawnpoint = 0
        self.speed = CAR_SPEED
        self.color = (0, 255, 0)
        self.road = None
        self.line = None
        self.destinationRoad = None
        self.destinationLine = None
        self.passed = False

    def draw(self, screen):
        pg.draw.circle(screen, self.color, (self.x, self.y), CIRCLE_RAD)

    def update(self, screen, crossroad):
        if self.road != self.destinationRoad:
            if self.road.orientation == 'vertical':
                if abs(self.y - self.destinationLine.coordinate) < CAR_SPEED:
                    self.y = self.destinationLine.coordinate
                    self.road = self.destinationRoad
                    self.line = self.destinationLine

            else:
                if abs(self.x - self.destinationLine.coordinate) < CAR_SPEED:
                    self.x = self.destinationLine.coordinate
                    self.road = self.destinationRoad
                    self.line = self.destinationLine
        self.move(crossroad)
        self.draw(screen)

    def isOnCrossroad(self, crossroad):
        if crossroad.crossroadRect.left - CIRCLE_RAD < self.x < crossroad.crossroadRect.right + CIRCLE_RAD \
                and crossroad.crossroadRect.top - CIRCLE_RAD < self.y < crossroad.crossroadRect.bottom + CIRCLE_RAD:
            self.passed = True
            return True
        else:
            return False

    def wait(self):
        self.color = (self.color[0] + 0.5, self.color[1] - 0.5, 0)
        if self.color[0] > 255:
            self.color = (255, self.color[1], 0)
        if self.color[1] < 0:
            self.color = (self.color[0], 0, 0)

        self.waitingTime += 1 / 60

    def move(self, crossroad):
        is_able_to_move = True
        for car in self.line.carsOnLine:
            if not self.isOnCrossroad(crossroad) and car is not self:
                if self.line.direction == (-1, 0) and self.x < car.x or \
                        self.line.direction == (1, 0) and self.x > car.x or \
                        self.line.direction == (0, -1) and self.y < car.y or \
                        self.line.direction == (0, 1) and self.y > car.y:
                    continue
                if not self.passed and not car.passed:
                    d = self.distToCrossroad - car.distToCrossroad
                elif self.passed and car.passed:
                    d = car.distToCrossroad - self.distToCrossroad
                else:
                    continue
                if d < 2 * CIRCLE_RAD + OPTIMAL_DISTANCE:
                    is_able_to_move = False

        if not self.passed and self.line.trafficLightColor != 0:
            if self.distToCrossroad < CIRCLE_RAD + TRAFFIC_LIGHT_WIDTH // 2 + OPTIMAL_DISTANCE:
                is_able_to_move = False
        if is_able_to_move:
            self.speed += CAR_SPEED / 50
            if self.speed > CAR_SPEED:
                self.speed = CAR_SPEED
        else:
            self.speed -= CAR_SPEED / 2
            if self.speed < 0:
                self.speed = 0

            self.wait()

        self.x += self.speed * self.line.direction[0]
        self.y += self.speed * self.line.direction[1]
        delta = abs(self.speed * self.line.direction[0]) + abs(self.speed * self.line.direction[1])
        self.distToSpawnpoint += delta

        if not self.passed:
            self.distToCrossroad -= delta
        elif self.passed and not self.isOnCrossroad(crossroad):
            self.distToCrossroad += delta


def main(genomes, config):
    global ge, nets
    crossroads = []
    ge = []
    nets = []
    for genome_id, genome in genomes:
        crossroads.append(Crossroad())
        ge.append(genome)
        net = neat.nn.FeedForwardNetwork.create(genome, config)
        nets.append(net)
        genome.fitness = 0

    pg.init()
    font = pg.font.Font(None, 32)

    pg.display.set_caption("Traffic Manager")
    screen = pg.display.set_mode((SCREEN_SIZE[0], SCREEN_SIZE[1]))

    clock = pg.time.Clock()
    crossroad = crossroads[0]
    start_time = time.time()
    while True:
        for event in pg.event.get():
            if event.type == pg.QUIT:
                pg.quit()
                exit()
            elif event.type == pg.KEYDOWN:
                if event.key == pg.K_SPACE:
                    crossroad.isSwitched = not crossroad.isSwitched
        if random.randint(1, 60 // SPAWNRATE) == 1:
            crossroad.addCar()
        crossroad.display(screen)
        for road in crossroad.roads:
            for line in road.lines:
                line.spawnCar()

        idToBeDeleted = []
        for road in crossroad.roads:
            for line in road.lines:
                for car in line.carsOnLine:
                    if not -3 * CIRCLE_RAD < car.x < SCREEN_SIZE[0] + 3 * CIRCLE_RAD or \
                            not -3 * CIRCLE_RAD < car.y < SCREEN_SIZE[1] + 3 * CIRCLE_RAD:
                        idToBeDeleted.append(car.id)
                    car.update(screen, crossroad)

        for car_id in idToBeDeleted:
            for road in crossroad.roads:
                for line in road.lines:
                    for car in line.carsOnLine:
                        if car.id == car_id:
                            if car.waitingTime > crossroad.maxWaitingTime:
                                crossroad.maxWaitingTime = car.waitingTime
                            crossroad.sumWaitingTimeOfProcessedCars += car.waitingTime
                            crossroad.processedCars += 1
                            line.deleteCar(car_id)

        crossroad.trafficLightManagerAI()
        # crossroad.trafficLightManager()
        crossroad.updateStatistics()

        av_time = font.render(f'Average waiting time: {round(crossroad.averageTime, 2)} s', True, (255, 255, 255))
        max_time = font.render(f'Max waiting time: {round(crossroad.maxWaitingTime, 2)} s', True, (255, 255, 255))
        fitness = font.render(f'fitness: {round(100 - crossroad.maxWaitingTime - crossroad.averageTime / 2, 2)}',
                              True, (255, 255, 255))
        timer = font.render(f'{round(time.time() - start_time, 2)} s',
                            True, (255, 255, 255))
        screen.blit(av_time, [10, 10])
        screen.blit(max_time, [10, 40])
        screen.blit(fitness, [10, 70])
        screen.blit(timer, [1160, 10])

        pg.display.update()
        clock.tick(60)


def replay_genome(config_path, genome_path="traffic_manager_AI.pkl"):
    config = neat.config.Config(neat.DefaultGenome, neat.DefaultReproduction, neat.DefaultSpeciesSet,
                                neat.DefaultStagnation, config_path)

    with open(genome_path, "rb") as f:
        genome = pickle.load(f)

    genomes = [(1, genome)]
    main(genomes, config)


if __name__ == '__main__':
    replay_genome("config.txt")
