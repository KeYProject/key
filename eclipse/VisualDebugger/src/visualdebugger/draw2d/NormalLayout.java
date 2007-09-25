package visualdebugger.draw2d;

import java.util.List;

import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.draw2d.geometry.Transposer;

class NormalLayout extends BranchLayout {

NormalLayout(TreeBranch branch) {
	super(branch);
}

/**
 * @see org.eclipse.draw2d.examples.tree.BranchLayout#calculateDepth()
 */
void calculateDepth() {
	depth = 0;
	List subtrees = getSubtrees();
	for (int i = 0; i < subtrees.size(); i++)
		depth = Math.max(depth, ((TreeBranch)subtrees.get(i)).getDepth());
	depth++;
}

protected Dimension calculatePreferredSize(IFigure container, int wHint, int hHint) {
	Rectangle union = branch.getNodeBounds().getCopy();
//	if (branch.isExpanded())
		union.union(branch.getContentsPane().getBounds());
	
	return union.getSize();
}

public void layout(IFigure f) {
//	Animation.recordInitialState(f);
//	if (Animation.playbackState(f))
//		return;

	Transposer transposer = getTransposer();
	IFigure contents = branch.getContentsPane();
	IFigure node = branch.getNode();
	contents.validate();

	Rectangle branchBounds = transposer.t(branch.getBounds());
	Point topLeft = branchBounds.getTopLeft();
	Rectangle nodeLocation = new Rectangle(topLeft, transposer.t(node.getPreferredSize()));
	nodeLocation.height = rowHeight - getMajorSpacing();
	
	if (!contents.isVisible() || contents.getChildren().isEmpty()) {
		nodeLocation.x += (branchBounds.width - nodeLocation.width)/2;
		node.setBounds(transposer.t(nodeLocation));
		contents.setBounds(
			transposer.t(nodeLocation.getTranslated(0, rowHeight).setSize(0, 0)));
		return;
	}

	Rectangle contentsLocation =
		new Rectangle(topLeft, transposer.t(contents.getPreferredSize()));
	contents.setSize(contents.getPreferredSize());
	contentsLocation.y += rowHeight;

	TreeBranch firstChild = (TreeBranch)contents.getChildren().get(0);
	TreeBranch lastChild =
		(TreeBranch)contents.getChildren().get(contents.getChildren().size() - 1);
	int leftInset =
		firstChild.getContourLeft()[0]
			+ transposer.t(firstChild.getBounds()).x
			- transposer.t(contents.getBounds()).x;
	int rightInset =
		lastChild.getContourRight()[0]
			- transposer.t(lastChild.getBounds()).right()
			+ transposer.t(contents.getBounds()).right();
	rightInset = Math.max(rightInset, 0);
	leftInset = Math.max(leftInset, 0);
	int childrenSpan = contentsLocation.width - leftInset - rightInset;

	switch (branch.getAlignment()) {
		case PositionConstants.CENTER :
			leftInset += (childrenSpan - nodeLocation.width) / 2;
	}

	if (leftInset > 0)
		nodeLocation.x += leftInset;
	else
		contentsLocation.x -= leftInset;
	
	int adjust =
		branchBounds.width
			- Rectangle.SINGLETON.setBounds(contentsLocation).union(nodeLocation).width;
	adjust /= 2;
	nodeLocation.x += adjust;
	contentsLocation.x += adjust;
	if (node instanceof SourceElementFigure || node instanceof MethodInvocationFigure
                || node instanceof MethodReturnFigure) //TODO
        node.setBounds(transposer.t(nodeLocation));
        else node.setBounds(transposer.t(nodeLocation).setSize(10, 10));
//	Animation.setBounds(node, transposer.t(nodeLocation));
//	Animation.setBounds(contents, transposer.t(contentsLocation));
	contents.setBounds(transposer.t(contentsLocation));
}

void mergeContour(int[] destination, int[] source, int startdepth, int offset) {
	for (int i = startdepth; i<source.length; i++)
		destination[i+1] = source[i] + offset;
}

/**
 * @see org.eclipse.draw2d.examples.tree.BranchLayout#paintLines(org.eclipse.draw2d.Graphics)
 */
void paintLines(Graphics g) {
    
    if (true)
        return; //TODO
    
	if (getTransposer().isEnabled()) {
		IFigure node = branch.getNode();
		int left = node.getBounds().right();
		int right = branch.getContentsPane().getBounds().x - 1;
		int yMid = node.getBounds().getCenter().y;
		int xMid = (left + right) / 2;
		List children = getSubtrees();
		if (children.size() == 0)
			return;
		g.drawLine(left, yMid, xMid, yMid);
		int yMin = yMid;
		int yMax = yMid;
		for (int i=0; i<children.size(); i++){
			int y = ((TreeBranch)children.get(i)).getNodeBounds().getCenter().y;
			g.drawLine(xMid, y, right, y);
			yMin = Math.min(yMin, y);
			yMax = Math.max(yMax, y);
		}
		g.drawLine(xMid, yMin, xMid, yMax);

	} else {
		IFigure node = branch.getNode();
		int xMid = node.getBounds().getCenter().x;
		int top = node.getBounds().bottom();
		int bottom = branch.getContentsPane().getBounds().y - 1;
		int yMid = (top + bottom) / 2;
		List children = getSubtrees();
		if (children.size() == 0)
			return;
		g.drawLine(xMid, top, xMid, yMid);
		int xMin = xMid;
		int xMax = xMid;
		for (int i=0; i<children.size(); i++){
			int x = ((TreeBranch)children.get(i)).getNodeBounds().getCenter().x;
			g.drawLine(x, yMid, x, bottom);
			xMin = Math.min(xMin, x);
			xMax = Math.max(xMax, x);
		}
		g.drawLine(xMin, yMid, xMax, yMid);
	}
}

/**
 * @see org.eclipse.draw2d.examples.tree.BranchLayout#updateContours()
 */
void updateContours() {
	Transposer transposer = getTransposer();
	//Make sure we layout first
	branch.validate();

	cachedContourLeft = new int[getDepth()];
	cachedContourRight = new int[getDepth()];

	Rectangle clientArea =
		transposer.t(branch.getNodeBounds().getUnion(branch.contents.getBounds()));
	Rectangle nodeBounds = transposer.t(branch.getNodeBounds());
	Rectangle contentsBounds = transposer.t(branch.getContentsPane().getBounds());
	
	cachedContourLeft[0] = nodeBounds.x - clientArea.x;
	cachedContourRight[0] = clientArea.right() - nodeBounds.right();
//	if (!branch.isExpanded())
//		return;

	List subtrees = getSubtrees();
	TreeBranch subtree;

	int currentDepth = 0;
	for (int i = 0; i < subtrees.size() && currentDepth < getDepth(); i++) {
		subtree = (TreeBranch)subtrees.get(i);
		if (subtree.getDepth() > currentDepth) {
			int leftContour[] = subtree.getContourLeft();
			int leftOffset = transposer.t(subtree.getBounds()).x - clientArea.x;
			mergeContour(cachedContourLeft, leftContour, currentDepth, leftOffset);
			currentDepth = subtree.getDepth();
		}
	}

	currentDepth = 0;
	for (int i = subtrees.size() - 1; i >= 0 && currentDepth < getDepth(); i--) {
		subtree = (TreeBranch)subtrees.get(i);
		if (subtree.getDepth() > currentDepth) {
			int rightContour[] = subtree.getContourRight();
			int rightOffset =
				clientArea.right() - transposer.t(subtree.getBounds()).right();
			mergeContour(cachedContourRight, rightContour, currentDepth, rightOffset);
			currentDepth = subtree.getDepth();
		}
	}
}

/**
 * @see org.eclipse.draw2d.examples.tree.BranchLayout#updateRowHeights()
 */
void updateRowHeights() {
	Transposer transposer = getTransposer();
	preferredRowHeights = new int[getDepth()];

	preferredRowHeights[0] =
		transposer.t(branch.getNode().getPreferredSize()).height + getMajorSpacing();

//	if (!branch.isExpanded())
//		return;

	List subtrees = getSubtrees();
	TreeBranch subtree;
	
	for (int i = 0; i < subtrees.size(); i++) {
		subtree = (TreeBranch)subtrees.get(i);
		int rowHeights[] = subtree.getPreferredRowHeights();
		for (int row = 0; row < rowHeights.length; row++)
			preferredRowHeights[row + 1] =
				Math.max(preferredRowHeights[row + 1], rowHeights[row]);
	}
}

/**
 * @see org.eclipse.draw2d.examples.tree.BranchLayout#setRowHeights(int[], int)
 */
void setRowHeights(int[] heights, int offset) {
	super.setRowHeights(heights, offset);
	if (true/*branch.isExpanded()*/) {
		List subtrees = getSubtrees();
		offset++;
		for (int i=0; i<subtrees.size(); i++)
			((TreeBranch)subtrees.get(i)).setRowHeights(heights, offset);
	}
}

}
