# Project objectives

The main goal of this project is to write and prove a certain algorithm. 
* First, this algorithm decomposes a given bidimensional euclidian space composed of obstacles into cells, in which there are no obstacles
* It then creates a graph which nodes are the cells and there is a link between two nodes when there is no obstacle between the corresponding cells.
* It is then possible to find a path between any given two points in the plane, as long as the cells they are in are connected in the graph by a simple graph traversing.


## Cell Decomposition 

We want to divide the space into multiple cells and to know which points are composing the cells.

### The input must be prepocessed as follows : 
* a list of event. 
    * an event is the start or the end of an edge, the data structure contains a point and all of the incoming and outgoing edges (an edge is incoming relatively to an edge if it ends at that event, considered from left to right and is outgoing if it starts at that event).
    * if two edges are crossing on the original drawing they must be divided into 4 sub-edges in the manner that no edges are crossing.
* two edges, constituing the "box" in which we're making cells,
    * every event (and by consequence every edge linked to those events) must be between those two edges.
    * there are no strong prerequisite on the shape of the box edges besides the one previously stated.

### The output has the following properties,
* the algorithm outputs a list of cells
* each cell contains a list of points and their lower and higher edge
* every point of the original plane is in a cell


### The algorithm goes as follows 

* it starts with an empty list of events. When it encounters the first event, it divides the space according to the number of its outgoing edges. In the case where the original plane has an empty space on the left or the right, we can just add events without any edges at the extreme left or extreme right of the plane.

* 