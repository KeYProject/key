package visualdebugger.draw2d;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.draw2d.Connection;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.geometry.Transposer;

public class TreeRoot extends TreeBranch {

private int major = 100;
private Transposer transposer = new Transposer();
private int minor = 100;
private LinkedList labels= new LinkedList();

public void setHorizontal(boolean value) {
        transposer.setEnabled(!value);
        invalidateTree();
        revalidate();
}


/**
 * @param title
 */
public TreeRoot(IFigure title) {
	super(title,null);
}


public int getMajorSpacing() {
	return major;
}

public void addLabel(Connection con){
    labels.add(con);
    add(con);
}

public void removeLabels(){
    Iterator it = labels.iterator();
    while(it.hasNext()){
        remove((Connection)it.next());
    }
    labels.clear();
}

public boolean containsPoint(int x, int y) {
    if ( node.containsPoint(x, y) || contents.containsPoint(x, y))
        return true;
    Iterator it = labels.iterator();
    while(it.hasNext()){
        if (((Connection)it.next()).containsPoint(x, y))
        return true;
    }

    return false;
}


/**
 * @return
 */
public int getMinorSpacing() {
	return minor;
}

public TreeRoot getRoot() {
	return this;
}



/**
 * sets the space (in pixels) between this branch's node and its subtrees.
 */
public void setMajorSpacing(int value) {
	this.major = value;
	invalidateTree();
	revalidate();
}


public Transposer getTransposer() {
        return transposer;
}


public boolean isHorizontal() {
        return !transposer.isEnabled();
}

/**
 * @param i
 */
public void setMinorSpacing(int i) {
	minor = i;
	invalidateTree();
	revalidate();
}

/**
 * @see org.eclipse.draw2d.Figure#validate()
 */

public void validate() {
        if (isValid())
                return;
        setRowHeights(getPreferredRowHeights(), 0);
        super.validate();
}



}
