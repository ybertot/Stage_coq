# Vertical Cell Decomposition

## The algorithm

This development contains a program to decompose a workspace into cells that
are free of obstacles.  The workspace is given by a top and a bottom
edges (which cannot be vertical).  The obstacles are also given by non-vertical
edges.

The program works in two phases.  In a first phase a collection of event
is created.  Each event has a location (a point in the workspace), and the
events are stored in a list that is sorted lexicographically with respect
to their location.  Each event contains an extra field containing all the
edges whose leftmost extremity is located on the same point.

The second phase processes the events in the order given by the sequence,
maintaining a list of open cells and a set of closed cells in the process.
Each time an event is processed, some of the open cells are closed and added
to the set of closed cells.  The open cells that are not in contact with the
event being processed remain in the list of open cell for later, the cells
that are in contact with the event being processed are usually closed, except
when they only need to be updated.  This happens when there is no edge
whose leftmost extremity is this event and the event is between the left
bottom corner and the left top corner of the cell.

Careful treatment is needed when successive events are on the same vertical
line.  In this case, it may be necessary to avoid closing a cell that was
just created and would be flat.  Instead, the location of the new event should
be added among the obstacles appearing on the cell side.  A similar treatment
may be necessary for the last created closed ceell.

## The proof

We prove a large invariant concerning the sequence of open cells.  This
sequence should be ordered vertically, all open cells should be "alive" with
respect to the next event, etc.