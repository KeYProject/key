package visualdebugger.views;

import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.VariableDeclarationStatement;
import org.eclipse.jface.text.Document;
import org.eclipse.swt.*;
import org.eclipse.swt.events.*;
import org.eclipse.swt.layout.*;
import org.eclipse.swt.widgets.*;

// TODO: Auto-generated Javadoc
/**
 * The Class WatchExpressionDialog.
 */
public class WatchExpressionDialog {

	/** The shell. */
	private Shell shell;

	/** The expression. */
	private String expression;

	/** The expression. */
	private String source;
	/** The text. */
	private Text text;

	private int line;

	/**
	 * Instantiates a new watch expression dialog.
	 * 
	 * @param parent
	 *            the parent
	 */
	public WatchExpressionDialog(Shell parent, int line, String source) {
		shell = new Shell(parent, SWT.DIALOG_TRIM | SWT.PRIMARY_MODAL);
		shell.setText("Enter watch expression");
		shell.setLayout(new GridLayout());
		this.source = source;
		this.line = line;
	}

	/**
	 * Creates the control buttons.
	 */
	private void createControlButtons() {
		Composite composite = new Composite(shell, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.HORIZONTAL_ALIGN_CENTER));
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);

		Button okButton = new Button(composite, SWT.PUSH);
		okButton.setText("OK");
		okButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {

				if (isValid(text.getText())) {

					expression = text.getText();
					shell.close();
				} else {
					// if expression is not valid clear values
					expression = null;
					shell.close();
				}
			}
		});

		Button cancelButton = new Button(composite, SWT.PUSH);
		cancelButton.setText("Cancel");
		cancelButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				expression = null;
				shell.close();
			}
		});

		shell.setDefaultButton(okButton);
	}

	/**
	 * Checks if the given expression is valid in this context.
	 * 
	 * @param expression
	 *            the expression
	 * 
	 * @return true, if expression is valid
	 */
	protected boolean isValid(String expression) {
		// TODO Auto-generated method stub
		String temp_var = "dummy =" + expression;

		Document doc = new Document(source);
		ASTParser parser = ASTParser.newParser(AST.JLS3);
		parser.setSource(doc.get().toCharArray());
		CompilationUnit cu = (CompilationUnit) parser.createAST(null);
		cu.recordModifications();
		AST ast = cu.getAST();
		
		VariableDeclarationFragment vdf = ast.newVariableDeclarationFragment();
		vdf.setName(ast.newSimpleName("dummy"));
		VariableDeclarationStatement vds = ast.newVariableDeclarationStatement(vdf);
		
		vds.setType(ast.newSimpleType(ast.newSimpleName("boolean")));
		
		// id.setName(ast.newName(new String[] {"java", "util", "Set"});
		// cu.imports().add(id); // add import declaration at end

		return true;
	}

	/**
	 * Creates the text widget.
	 */
	private void createTextWidget() {
		
		Composite composite = new Composite(shell, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);

		Label label = new Label(composite, SWT.RIGHT);
		label.setText("Expression:");
		text = new Text(composite, SWT.BORDER);
		GridData gridData = new GridData();
		gridData.widthHint = 400;
		text.setLayoutData(gridData);

	}

	/**
	 * Gets the title.
	 * 
	 * @return the title
	 */
	public String getTitle() {
		return shell.getText();
	}

	/**
	 * Returns the contents of the <code>Text</code> widgets in the dialog in
	 * a <code>String</code> array.
	 * 
	 * @return String[] The contents of the text widgets of the dialog. May
	 *         return null if all text widgets are empty.
	 */
	public String getExpression() {
		return expression;
	}

	/**
	 * Opens the dialog in the given state. Sets <code>Text</code> widget
	 * contents and dialog behaviour accordingly.
	 * 
	 * @return the string
	 */
	public String open() {
		createTextWidget();
		createControlButtons();
		shell.pack();
		shell.open();
		Display display = shell.getDisplay();
		while (!shell.isDisposed()) {
			if (!display.readAndDispatch())
				display.sleep();
		}

		return getExpression();
	}
}
