package visualdebugger.draw2d;


import org.eclipse.swt.SWT;
import org.eclipse.swt.events.*;
import org.eclipse.swt.layout.*;
import org.eclipse.swt.widgets.*;

public class RoundedRectangleExample {
  private Text txtArcWidth = null;
  private Text txtArcHeight = null;

  /**
   * Runs the application
   */
  public void run() {
    Display display = new Display();
    Shell shell = new Shell(display);
    shell.setText("RoundRectangle Example");
    createContents(shell);
    shell.open();
    while (!shell.isDisposed()) {
      if (!display.readAndDispatch()) {
        display.sleep();
      }
    }
    display.dispose();
  }

  /**
   * Creates the main window's contents
   * 
   * @param shell the main window
   */
  private void createContents(Shell shell) {
    shell.setLayout(new FillLayout(SWT.VERTICAL));

    // Create the composite that holds the input fields
    Composite widgetComposite = new Composite(shell, SWT.NONE);
    widgetComposite.setLayout(new GridLayout(2, false));

    // Create the input fields
    new Label(widgetComposite, SWT.NONE).setText("Arc Width:");
    txtArcWidth = new Text(widgetComposite, SWT.BORDER);

    new Label(widgetComposite, SWT.NONE).setText("Arc Height");
    txtArcHeight = new Text(widgetComposite, SWT.BORDER);

    // Create the button that launches the redraw
    Button button = new Button(widgetComposite, SWT.PUSH);
    button.setText("Redraw");
    shell.setDefaultButton(button);

    // Create the canvas to draw the round rectangle on
    final Canvas drawingCanvas = new Canvas(shell, SWT.NONE);
    drawingCanvas.addPaintListener(new RoundRectangleExamplePaintListener());

    // Add a handler to redraw the round rectangle when pressed
    button.addSelectionListener(new SelectionAdapter() {
      public void widgetSelected(SelectionEvent e) {
        drawingCanvas.redraw();
      }
    });
  }

  /**
   * This class gets the user input and draws the requested round rectangle
   */
  private class RoundRectangleExamplePaintListener implements PaintListener {
    public void paintControl(PaintEvent e) {
      // Get the canvas for drawing and its width and height
      Canvas canvas = (Canvas) e.widget;
      int x = canvas.getBounds().width;
      int y = canvas.getBounds().height;

      // Determine user input, defaulting everything to zero.
      // Any blank fields are converted to zero
      int arcWidth = 0;
      int arcHeight = 0;
      try {
        arcWidth = txtArcWidth.getText().length() == 0 ? 0 : Integer
            .parseInt(txtArcWidth.getText());
        arcHeight = txtArcWidth.getText().length() == 0 ? 0 : Integer
            .parseInt(txtArcHeight.getText());
      } catch (NumberFormatException ex) {
        // Any problems, set them both to zero
        arcWidth = 0;
        arcHeight = 0;
      }

      // Set the line width
      e.gc.setLineWidth(2);

      // Draw the round rectangle
      e.gc.drawRoundRectangle(10, 10, x - 20, y - 20, arcWidth, arcHeight);
    }
  }

  /**
   * The application entry point
   * 
   * @param args the command line arguments
   */
  public static void main(String[] args) {
    new RoundedRectangleExample().run();
  }
}