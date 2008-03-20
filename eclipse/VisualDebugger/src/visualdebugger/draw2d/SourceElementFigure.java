package visualdebugger.draw2d;

import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.ColorConstants;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.StackLayout;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Expression;
import org.eclipse.jdt.core.dom.Statement;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;

import de.uka.ilkd.key.visualdebugger.ETNode;
import de.uka.ilkd.key.visualdebugger.ETStatementNode;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class SourceElementFigure extends Figure {

    private boolean selected;

    static final Color gradient1 = new Color(null, 232, 232, 240);

    static final Color gradient2 = new Color(null, 176, 184, 216);

    static final Color gradient12 = new Color(null, 236, 152, 188);

    static final Color gradient22 = new Color(null, 236, 196, 213);

    static final Color corner1 = new Color(null, 200, 208, 223);

    static final Color corner2 = new Color(null, 160, 172, 200);

    static final Color blue = new Color(null, 152, 168, 200);

    static final Color shadow = new Color(null, 202, 202, 202);

    static final int CORNER_SIZE = 00;

    ETNode etNode = null;

    final ETStatementNode sNode;

    Statement statement;

    Expression expression;

    ICompilationUnit unit;

    // static final Border BORDER = new CompoundBorder(new FoldedPageBorder(),
    // new MarginBorder(4, 4, 8, 3));
    static final Border BORDER = new LineBorder(ColorConstants.black, 1);

    static final Border BREAKMODEBORDER = new LineBorder(ColorConstants.red, 2);

    static final Border ROUNDEDBORDER = new RoundedBorder(ColorConstants.black,
            1);

    public static class RoundedBorder extends LineBorder {

        public RoundedBorder(Color color, int width) {
            super(color, width);
        }

        public void paint(IFigure figure, Graphics graphics, Insets insets) {
            tempRect.setBounds(getPaintRectangle(figure, insets));
            if (getWidth() % 2 == 1) {
                tempRect.width--;
                tempRect.height--;
            }
            tempRect.shrink(getWidth() / 2, getWidth() / 2);
            graphics.setLineWidth(getWidth());
            if (getColor() != null)
                graphics.setForegroundColor(getColor());
            graphics.drawRoundRectangle(tempRect, 12, 12);
        }
    }

    private Label label = new Label();

    public SourceElementFigure(String text) {
        this();
        if (text.length() > 20)
            text = text.substring(0, 20);
        label.setFont(Display.getCurrent().getSystemFont());
        label.setText(text);
    }

    public SourceElementFigure() {
        setBorder(BORDER);
        setLayoutManager(new StackLayout());
        add(label);
        sNode = null;
        statement = null;
        unit = null;
    }

    public SourceElementFigure(ETStatementNode etNode) {
        // this();

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
            expression = visualdebugger.Activator.getDefault().getExpression(etNode.getStatementId());
            setBorder(ROUNDEDBORDER);
            unit = visualdebugger.Activator.getDefault().getCompilationUnit(
                    etNode.getStatementId());          
            st = expression.toString();            
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

    public void setSelected(boolean value) {
        this.selected = value;
        if (selected)
            label.setForegroundColor(ColorConstants.white);
        else
            label.setForegroundColor(null);
        repaint();
    }

    /**
     * @see java.lang.Object#toString()
     */
    public String toString() {
        // return ((Label) getChildren().get(0)).getText();
        if (getETNode() != null)
            if (getETNode().getITNodesArray()[0] != null)
                return getETNode().getITNodesArray()[0].getId() + "";

        return "nullds";
    }

    public void validate() {
        repaint();
        super.validate();
    }

    public ETNode getETNode() {
        return sNode;
    }

    public Statement getStatement() {
        return statement;
    }

    public ICompilationUnit getUnit() {
        return unit;
    }

    public ASTNode getASTNode() {
        if (statement != null)
            return statement;
        else
            return expression;
    }

}
