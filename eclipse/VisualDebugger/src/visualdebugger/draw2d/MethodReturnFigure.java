package visualdebugger.draw2d;

import org.eclipse.draw2d.*;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.swt.graphics.Color;

import de.uka.ilkd.key.visualdebugger.VisualDebugger;
import de.uka.ilkd.key.visualdebugger.executiontree.ETMethodReturnNode;

public class MethodReturnFigure extends Figure implements DrawableNode {

    private boolean selected;

    static final Color gradient1 = new Color(null, 132, 132, 240);

    static final Color gradient2 = new Color(null, 76, 84, 216);

    static final Color gradient12 = new Color(null, 202, 202, 210);

    static final Color gradient22 = new Color(null, 146, 154, 186);

    static final Color corner1 = new Color(null, 200, 208, 223);

    static final Color corner2 = new Color(null, 160, 172, 200);

    static final Color blue = new Color(null, 152, 168, 200);

    static final Color shadow = new Color(null, 202, 202, 202);

    static final int CORNER_SIZE = 00;

    final ETMethodReturnNode mrNode;

    static final Border BORDER = new LineBorder(ColorConstants.black, 1);

    private Label label = new Label();

    public MethodReturnFigure(ETMethodReturnNode etNode) {
        super();
        setBorder(BORDER);
        setLayoutManager(new StackLayout());

        add(label);

        this.mrNode = etNode;

        String st;
        if (mrNode.getResult() != null)
            st = "return "
                    + VisualDebugger.getVisualDebugger().prettyPrint(
                            mrNode.getResult());
        else
            st = "return";

        label.setText(st);

        String toolTip = "Returned from method:\n "
                + VisualDebugger.getMethodString(mrNode.getParent()
                        .getLastMethodInvocation().getMethod()
                        .getMethodDeclaration());

        this.setToolTip(new Label(toolTip));
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

            // g.setForegroundColor(gradient1);
            // g.setBackgroundColor(gradient2);

            g.setForegroundColor(ColorConstants.white);
            g.setBackgroundColor(ColorConstants.white);

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
        return ((Label) getChildren().get(0)).getText();
    }

    public void validate() {
        repaint();
        super.validate();
    }

    public ETMethodReturnNode getETNode() {
        return mrNode;
    }

}
