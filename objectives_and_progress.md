# Project objectives

The main goal of this project is to write and prove a certain algorithm. 
* First, this algorithm decomposes a given bidimensional euclidian space composed of obstacles into cells, in which there are no obstacles.
* It then creates a graph whose nodes are the cells and there is a link between two nodes when there is no obstacle between the corresponding cells.
* It is then possible to find a path between any given two points in the plane, as long as the cells they are in are connected in the graph by a simple graph traversal.


## Cell Decomposition 

We want to divide the space into multiple cells and to know which points are composing the cells.

### The input must be prepocessed as follows : 
* a list of event. 
    * an event is the start or the end of an edge, the data structure contains a point and all of the incoming and outgoing edges (an edge is incoming relatively to an edge if it ends at that event, considered from left to right and is outgoing if it starts at that event).
    * if two edges are crossing on the original drawing they must be divided into 4 sub-edges in the manner that no edges are crossing.
    1. The list of events must verify that all edges starting from an event will be closed in a following one (ie all edges in the outgoing list from an event must be in an incoming list from another event that is later in the list) verified by function close_edges_from_events.  This imposes that edges move from left to right.
    2. for a certain event, every right extremity of its incoming edges must be equal to the left extremity of its outgoing edges and must be equal to the point of that event.
    
* two edges, the top edge and the bottom edge, constituting the "box" in
  which we are making cells,
    * every event (and by consequence every edge linked to those events) must be between those two edges.
    * there are no strong prerequisite on the shape of the box edges besides the one previously stated.

### The output has the following properties,
* the algorithm outputs a list of cells
* each cell contains a list of points and their lower and higher edge
* every point between the top edge and the bottom edge (vertically) and between
  the first and the last event (horizontally) is in a cell.


### The algorithm goes as follows 

* it starts with an empty list of cells. When it encounters the first event, it divides the space between the top and the bottom edge according to the number of its outgoing edges. In the case where the original plane has an empty space on the left or the right, we can just add events without any edges at the extreme left or extreme right of the plane.

* the algorithms scans the space from left to right using the list of events, assuming it is sorted from lowest abscissa to highest, and knowing that no two events can have the same abscissa.

* at each step the algorithm treats a new event, closing cells and opening new ones, thus maintaining a list of closed cells and a list of alive cells. 
    1. It must keep the alive cells sorted from lowest second coordinate to highest one. 
    2. Each edge constituting one of the alive cells will be closed in the list of remaining events, except the edges constituting the box.
    3. The alive cells must all be adjacent to the following and previous cells, meaning there is no hole for a certain abscissa. (every point will be in an alive cell that will end up closed, and thus every point will be in a cell in the end).
The property in code end_edge takes an edge and a list of event and is true if the edge is bottom or top or if the edge is closed by a future event.
The lemma opening_cells_close verifies that when creating new cells(with the opening_cells function), when the lower edge and higher edge verifies the end_edge property, all new cells have the properties that every cell created has edges that close. 

* after the last event is treated, there are no more alive cells and we return the list of closed cells, corresponding to the cell decomposition we were looking for. 
The way to search for adjacence between each cell in the graph should be that every cell having two points in common are adjacent, except if those two points constitute an edge (since each cell contains the lower and higher edge, there is an easy way to check).