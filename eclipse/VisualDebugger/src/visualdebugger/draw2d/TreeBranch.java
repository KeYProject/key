package visualdebugger.draw2d;

import java.util.Iterator;
import java.util.List;

import org.eclipse.draw2d.ChopboxAnchor;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.Connection;
import org.eclipse.draw2d.ConnectionEndpointLocator;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FlowLayout;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.Layer;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.MidpointLocator;
import org.eclipse.draw2d.PolygonDecoration;
import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.RelativeLocator;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.draw2d.Viewport;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.uka.ilkd.key.proof.Node;

public class TreeBranch extends Figure {

    class AnimatingLayer extends Layer {

        /**
         * @see org.eclipse.draw2d.Figure#setBounds(org.eclipse.draw2d.geometry.Rectangle)
         */
        public void setBounds(Rectangle rect) {

            int x = bounds.x, y = bounds.y;

            boolean resize = (rect.width != bounds.width)
                    || (rect.height != bounds.height), translate = (rect.x != x)
                    || (rect.y != y);

            if (isVisible() && (resize || translate))
                erase();
            if (translate) {
                int dx = rect.x - x;
                int dy = rect.y - y;
                primTranslate(dx, dy);
            }
            bounds.width = rect.width;
            bounds.height = rect.height;
            // if (resize) Layouts dont depend on size.
            // invalidate();
            if (resize || translate) {
                fireMoved();
                repaint();
            }
        }

    }

    int aligment = PositionConstants.CENTER;

    IFigure contents = new AnimatingLayer();

    boolean expanded = true;

    IFigure node;
    
    TreeBranch parentTB=null;

    private Connection connection;

    public TreeBranch(IFigure title, TreeBranch parent) {
        setLayoutManager(new NormalLayout(this));
        this.parentTB=parent;
        contents.setLayoutManager(new TreeLayout());
        // setLayoutManager(new ToolbarLayout());
        // contents.setLayoutManager(new FlowLayout());

//        if (title.getBorder() == null) TODO
//            title.setBorder(new LineBorder(ColorConstants.gray, 2));
        this.node = title;
        add(contents);
        add(title);

    }

    public void addBranch(TreeBranch b) {
        contents.add(b);
        repaint();
    }
    
    public void addBranch(TreeBranch b,String label) {
       contents.add(b);
        repaint();
    }


  
    /**
     * @see org.eclipse.draw2d.Figure#containsPoint(int, int)
     */
    public boolean containsPoint(int x, int y) {
        return node.containsPoint(x, y) || contents.containsPoint(x, y);
    }

    public int getAlignment() {
        return aligment;
    }

    protected BranchLayout getBranchLayout() {
        return (BranchLayout) getLayoutManager();
    }

    public IFigure getContentsPane() {
        return contents;
    }

    public int[] getContourLeft() {
        return getBranchLayout().getContourLeft();
    }

    public int[] getContourRight() {
        return getBranchLayout().getContourRight();
    }

    public int getDepth() {
        return getBranchLayout().getDepth();
    }

    /**
     * @see org.eclipse.draw2d.Figure#getMinimumSize(int, int)
     */
    public Dimension getMinimumSize(int wHint, int hHint) {
        return super.getMinimumSize(wHint, hHint);
    }

    public IFigure getNode() {
        return node;
    }

    public Rectangle getNodeBounds() {
        return node.getBounds();
    }

    public int[] getPreferredRowHeights() {
        return getBranchLayout().getPreferredRowHeights();

    }

    /**
     * @see org.eclipse.draw2d.Figure#getPreferredSize(int, int)
     */
    public Dimension getPreferredSize(int wHint, int hHint) {
        validate();
        return super.getPreferredSize(wHint, hHint);
    }

    public TreeRoot getRoot() {
        return ((TreeBranch) getParent().getParent()).getRoot();
    }

    /**
     * @see org.eclipse.draw2d.Figure#paintFigure(org.eclipse.draw2d.Graphics)
     */
    protected void paintFigure(Graphics graphics) {
        super.paintFigure(graphics);
    }

    public void setNode(IFigure node) {
        remove(this.node);
        add(node, 0);
    }

    public void setRowHeights(int heights[], int offset) {
        getBranchLayout().setRowHeights(heights, offset);
    }

    /**
     * @see java.lang.Object#toString()
     */
    public String toString() {
        return toString(0);
    }

    public String toString(int level) {
        String result = "";
        for (int i = 0; i < level; i++)
            result += "  ";
        result += getChildren().get(1) + "\n";
        for (int i = 0; i < contents.getChildren().size(); i++)
            result += ((TreeBranch) contents.getChildren().get(i))
                    .toString(level + 1);
        return result;
    }

    /**
     * @see org.eclipse.draw2d.Figure#validate()
     */
    public void validate() {
        if (isValid())
            return;

        //System.out.println("hallo");

        repaint();
        super.validate();
    }
    
    public void setConnection(Connection con){
        this.connection = con;
    }
    
    public Connection getConnection(){
        return this.connection;
    }

    public TreeBranch getParentTB() {
        return parentTB;
    }
    
//    public String toString(){
//      
//    }
    
    public void markBranch(){
        if (connection!=null)
            connection.setForegroundColor(ColorConstants.red);
        if (!(getParentTB() instanceof TreeRoot)&&getParentTB()!=null){
            getParentTB().markBranch();
        }
        
    }
    
    
    public TreeBranch findNode(Node n){
         if (getNode() instanceof LeafNode){
             LeafNode ln = (LeafNode)getNode();
             if(ln.getETLeafNode().representsProofTreeNode(n))
                 return this;
         }
         Iterator children = getContentsPane().getChildren().iterator();
         while(children.hasNext()){
            TreeBranch cp = (TreeBranch) children.next();
            TreeBranch result = cp.findNode(n);
            if (result!=null)
                return result;
            
         }        
        return null;
    }


}
