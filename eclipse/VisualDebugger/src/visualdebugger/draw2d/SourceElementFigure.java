package visualdebugger.draw2d;

import org.eclipse.draw2d.*;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.ETNode;
import de.uka.ilkd.key.visualdebugger.executiontree.ETStatementNode;

// TODO: Auto-generated Javadoc
/**
 * The Class SourceElementFigure.
 */
public class SourceElementFigure extends Figure implements DrawableNode {

    /** The selected. */
    private boolean selected;

    /** some color definitions. */
    static final Color collapseGradient = new Color(null, 155, 122, 34);
    static final Color gradient1 = new Color(null, 232, 232, 240);
    static final Color gradient2 = new Color(null, 176, 184, 216);
    static final Color gradient12 = new Color(null, 236, 152, 188);
    static final Color gradient22 = new Color(null, 236, 196, 213);
    static final Color corner1 = new Color(null, 200, 208, 223);
    static final Color corner2 = new Color(null, 160, 172, 200);
    static final Color blue = new Color(null, 152, 168, 230);

    /** The Constant shadow. */
    static final Color shadow = new Color(null, 202, 202, 202);

    /** The Constant CORNER_SIZE. */
    static final int CORNER_SIZE = 00;

    /** The s node. */
    final ETStatementNode sNode;

    /** The statement. */
    Statement statement;

    /** The expression. */
    Expression expression;

    /** The unit. */
    ICompilationUnit unit;

    // static final Border BORDER = new CompoundBorder(new FoldedPageBorder(),
    // new MarginBorder(4, 4, 8, 3));
    /** The Constant BORDER. */
    static final Border BORDER = new LineBorder(ColorConstants.black, 1);

    /** The Constant BREAKMODEBORDER. */
    static final Border BREAKMODEBORDER = new LineBorder(ColorConstants.red, 2);
    /** The Constant COLLAPSEDMODEBORDER. */
    static final Border COLLAPSEDMODEBORDER = new LineBorder(
            ColorConstants.lightGreen, 2);
    /** The Constant ACTIVEWATCHPOINTBORDER. */
    static final Border ACTIVEWATCHPOINTBORDER = new LineBorder(
            ColorConstants.orange, 2);

    /** The Constant ROUNDEDBORDER. */
    static final Border ROUNDEDBORDER = new RoundedBorder(ColorConstants.black,
            1);

    /**
     * The Class RoundedBorder.
     */
    public static class RoundedBorder extends LineBorder {

        /**
         * Instantiates a new rounded border.
         * 
         * @param color
         *            the color
         * @param width
         *            the width
         */
        public RoundedBorder(Color color, int width) {
            super(color, width);
        }

        /*
         * (non-Javadoc)
         * 
         * @see org.eclipse.draw2d.LineBorder#paint(org.eclipse.draw2d.IFigure,
         *      org.eclipse.draw2d.Graphics, org.eclipse.draw2d.geometry.Insets)
         */
        public void paint(IFigure figure, Graphics graphics, Insets insets) {
            tempRect.setBounds(getPaintRectangle(figure, insets));
            if (getWidth() % 2 == 1) {
                tempRect.width--;
                tempRect.height--;
            }
            tempRect.shrink(getWidth() / 2, getWidth() / 2);
            graphics.setLineWidth(getWidth());
            tempRect.crop(insets);
            if (getColor() != null)
                graphics.setForegroundColor(getColor());
            graphics.drawRoundRectangle(tempRect, 12, 12);

        }
    }

    /** The label. */
    private Label label = new Label();

    /**
     * Instantiates a new source element figure.
     * 
     * @param text
     *            the text
     */
    public SourceElementFigure(String text) {
        this();
        if (text.length() > 20)
            text = text.substring(0, 20);
        label.setFont(Display.getCurrent().getSystemFont());
        label.setText(text);
    }

    /**
     * Instantiates a new source element figure.
     */
    public SourceElementFigure() {
        setBorder(BORDER);
        setLayoutManager(new StackLayout());
        add(label);
        sNode = null;
        statement = null;
        unit = null;
    }

    /**
     * Instantiates a new source element figure.
     * 
     * @param etNode
     *            the et node
     */
    public SourceElementFigure(ETStatementNode etNode) {

        setLayoutManager(new StackLayout());
        add(label);
        String labelText = "";
        String st = "";
        boolean breakpoint = false;
        // if (etNode.getStatementId()!=null){
        if (etNode.getStatementId().isStatement()) {

            if (VisualDebugger.getVisualDebugger().getBpManager()
                    .suspendByBreakpoint(etNode.getStatementId())) {
                breakpoint = true;
                setBorder(BREAKMODEBORDER);
            } else
                setBorder(BORDER);
            statement = (Statement) visualdebugger.Activator.getDefault()
                    .getASTNodeForStatementId(etNode.getStatementId());

            unit = visualdebugger.Activator.getDefault().getCompilationUnit(
                    etNode.getStatementId());
            st = statement.toString();
        } else {
            expression = visualdebugger.Activator.getDefault().getExpression(
                    etNode.getStatementId());
            setBorder(ROUNDEDBORDER);
            unit = visualdebugger.Activator.getDefault().getCompilationUnit(
                    etNode.getStatementId());
            st = expression.toString();
        }
        if (etNode.isWatchpoint()) {
            setBorder(ACTIVEWATCHPOINTBORDER);
        } else {
            if (etNode.isCollapsed()) {
                setBorder(COLLAPSEDMODEBORDER);
            }
        }

        labelText = st;
        int i = st.indexOf("\n");
        if (i > -1)
            labelText = st.substring(0, i);
        label.setText(labelText);
        // }

        sNode = etNode;
        if (breakpoint)
            st = "Statement Breakpoint is reached...\n" + st;
        this.setToolTip(new Label(st));
    }

    /**
     * Paint figure.
     * 
     * @param g
     *            the g
     * 
     * @see org.eclipse.draw2d.Figure#paintFigure(org.eclipse.draw2d.Graphics)
     */
    protected void paintFigure(Graphics g) {
        super.paintFigure(g);

        if (selected) {
            g.setForegroundColor(ColorConstants.menuBackgroundSelected);
            g.setBackgroundColor(ColorConstants.titleGradient);
        } else {
            if (statement != null || label.getText().equals("Start")) {
                g.setForegroundColor(gradient1);
                g.setBackgroundColor(gradient2);
            } else {
                g.setForegroundColor(gradient12);
                g.setBackgroundColor(gradient22);

            }
        }
        g.fillGradient(getBounds().getResized(-1, -1), true);
    }

    /**
     * Sets the selected node. If a node is selected its text color is changed
     * to white.
     * 
     * @param value
     *            the new selected
     */
    public void setSelected(boolean isSelected) {
        this.selected = isSelected;
        if (selected)
            label.setForegroundColor(ColorConstants.white);
        else
            label.setForegroundColor(null);
        repaint();
    }

    /**
     * To string.
     * 
     * @return the string
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        // return ((Label) getChildren().get(0)).getText();
        if (getETNode() != null)
            if (getETNode().getITNodesArray()[0] != null)
                return getETNode().getITNodesArray()[0].getId() + "";

        return "nullds";
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.draw2d.Figure#validate()
     */
    public void validate() {
        repaint();
        super.validate();
    }

    /*
     * (non-Javadoc)
     * 
     * @see visualdebugger.draw2d.DrawableNode#getETNode()
     */
    public ETNode getETNode() {
        return sNode;
    }

    /**
     * Gets the statement.
     * 
     * @return the statement
     */
    public Statement getStatement() {
        return statement;
    }

    /**
     * Gets the unit.
     * 
     * @return the unit
     */
    public ICompilationUnit getUnit() {
        return unit;
    }

    /**
     * Gets the aST node.
     * 
     * @return the aST node
     */
    public ASTNode getASTNode() {
        if (statement != null)
            return statement;
        else
            return expression;
    }

}
