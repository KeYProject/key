package visualdebugger.draw2d;

import java.util.List;

import org.eclipse.draw2d.AbstractLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.draw2d.geometry.Transposer;

/**
 * Performs a layout on a container containing {@link AbstractBranch} figures. This layout is
 * similar to FlowLayout, except that the children are squeezed together to overlap by
 * comparing their left and right contours.
 * @author hudsonr
 * Created on Apr 18, 2003
 */
public class TreeLayout extends AbstractLayout {

private int pointOfContact;

/**
 * @see org.eclipse.draw2d.AbstractLayout#calculatePreferredSize(org.eclipse.draw2d.IFigure, int, int)
 */
protected Dimension calculatePreferredSize(IFigure container, int wHint, int hHint) {
	container.validate();
	List children = container.getChildren();
	Rectangle result =
		new Rectangle().setLocation(container.getClientArea().getLocation());
	for (int i = 0; i < children.size(); i++)
		result.union(((IFigure)children.get(i)).getBounds());
	result.resize(container.getInsets().getWidth(), container.getInsets().getHeight());
	return result.getSize();
}

private int[] calculateNewRightContour(int old[], int add[], int shift) {
	if (old == null)
		return add;
//	if (shift < 0)
//		shift = 0;
	int result[] = new int[Math.max(old.length, add.length)];
	System.arraycopy(add, 0, result, 0, add.length);
	for (int i = add.length; i < result.length; i++)
		result[i] = old[i] + shift;
	return result;
}

private int calculateOverlap(int leftSubtree[], int rightSubtree[]) {
	pointOfContact = 0;
	if (leftSubtree == null)
		return 0;
	int min = Math.min(leftSubtree.length, rightSubtree.length);
	int result = Integer.MAX_VALUE;
	for (int i=0; i<min; i++) {
		int current = leftSubtree[i] + rightSubtree[i];
		if (i > 0)
			current -= 5;
		if (current < result) {
			result = current;
			pointOfContact = i + 1;
		}
	}
	return result;
}

/**
 * @see org.eclipse.draw2d.LayoutManager#layout(org.eclipse.draw2d.IFigure)
 */
public void layout(IFigure container) {
//	Animation.recordInitialState(container);
//	if (Animation.playbackState(container))
//		return;
	TreeRoot root = ((TreeBranch)container.getParent()).getRoot();
	Transposer transposer = root.getTransposer();
	int gap = root.getMinorSpacing();
	List subtrees = container.getChildren();
	TreeBranch subtree;
	int previousSubtreeDepth = 0;
	int rightContour[] = null;
	int leftContour[];
	int contactDepth;
	
	Point reference = transposer.t(container.getBounds().getLocation());
	Point currentXY = reference.getCopy();
	
	for (int i = 0; i < subtrees.size(); i++) {
		subtree = (TreeBranch)subtrees.get(i);
		
		//Give the subtree its preferred size before asking for contours
		Dimension subtreeSize = subtree.getPreferredSize();
		subtree.setSize(subtreeSize);
		subtreeSize = transposer.t(subtreeSize);

		leftContour = subtree.getContourLeft();
		int overlap = calculateOverlap(rightContour, leftContour);
		//if (!subtree.getRoot().isCompressed())
			overlap = 0;
		contactDepth = pointOfContact;
		subtree.setLocation(transposer.t(currentXY.getTranslated(-overlap, 0)));

		//Setup value for next sibling
		int advance = gap + subtreeSize.width - overlap;
		rightContour = calculateNewRightContour(
			rightContour,
			subtree.getContourRight(),
			advance);
		currentXY.x += advance;
		
		/* 
		 * In some cases, the current child may extend beyond the left edge of the
		 * container because of the way it overlaps with the previous child. When this
		 * happens, shift all children right. 
		 */
		int shiftRight = reference.x - transposer.t(subtree.getBounds()).x;
		if (shiftRight > 0) {
			currentXY.x += shiftRight;
			Point correction = transposer.t(new Point(shiftRight, 0));
			for (int j=0; j<=i; j++)
				((IFigure)subtrees.get(j)).translate(correction.x, correction.y);
		}
		
		/*
		 * In some cases, the current child "i" only touches the contour of a distant
		 * sibling "i-n", where n>1.  This means that there is extra space that can be
		 * distributed among the intermediate siblings
		 */

		if (contactDepth > previousSubtreeDepth) {
			TreeBranch branch = (TreeBranch)subtrees.get(i-1);
			int slack =
				transposer.t(subtree.getBounds()).x
					- transposer.t(branch.getBounds()).right()
					- gap
					+ calculateOverlap(branch.getContourRight(), subtree.getContourLeft());
			int end = i;
			int begin = end - 1;
			while (begin > 0
				&& ((TreeBranch)subtrees.get(begin)).getDepth() < contactDepth)
				begin--;
			
			for (int j = begin + 1; j < end; j++) {
				branch = (TreeBranch)subtrees.get(j);
				Point shift =
					transposer.t(new Point(slack * (j - begin) / (end - begin), 0));
				branch.translate(shift.x, shift.y);
			}
		}
		previousSubtreeDepth = subtree.getDepth();
	}
}

}
