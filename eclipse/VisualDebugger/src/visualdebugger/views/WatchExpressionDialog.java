package visualdebugger.views;

import org.eclipse.swt.*;
import org.eclipse.swt.events.*;
import org.eclipse.swt.layout.*;
import org.eclipse.swt.widgets.*;

import sun.awt.HorizBagLayout;

public class WatchExpressionDialog {

	Shell shell;
	String[] values = new String[2];
	String[] labels = { "Expression:", "Scope:       " };
	Text text;

	public WatchExpressionDialog(Shell parent) {
		shell = new Shell(parent, SWT.DIALOG_TRIM | SWT.PRIMARY_MODAL);
		shell.setText("Enter watch expression");
		shell.setLayout(new GridLayout());
	}

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
					
					values[0] = text.getText();
					shell.close();
				} else {
					// if expression is not valid clear values
					values = null;
					shell.close();
				}
			}
		});

		Button cancelButton = new Button(composite, SWT.PUSH);
		cancelButton.setText("Cancel");
		cancelButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				values = null;
				shell.close();
			}
		});

		shell.setDefaultButton(okButton);
	}

	private void createScopeButtons() {
		Composite composite = new Composite(shell, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		composite.setLayout(layout);

		Label label = new Label(composite, SWT.LEFT);
		label.setText(labels[1]);

		Button globalButton = new Button(composite, SWT.RADIO | SWT.RIGHT);
		globalButton.setText("Global");
		globalButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				values[1] = "Global";
			}
		});

		Button localButton = new Button(composite, SWT.RADIO| SWT.RIGHT);
		localButton.setText("Local");
		localButton.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				values[1] = "Local";
			}
		});

		shell.setDefaultButton(globalButton);
	}

	protected boolean isValid(String str) {
		// TODO Auto-generated method stub
		// check if expression is valid in given context
		return true;
	}

	private void createTextWidgets() {

		Composite composite = new Composite(shell, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);

		Label label = new Label(composite, SWT.RIGHT);
		label.setText(labels[0]);
		text = new Text(composite, SWT.BORDER);
		GridData gridData = new GridData();
		gridData.widthHint = 400;
		text.setLayoutData(gridData);

	}

	public String[] getLabels() {
		return labels;
	}

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
	public String[] getValues() {
		return values;
	}

	/**
	 * Opens the dialog in the given state. Sets <code>Text</code> widget
	 * contents and dialog behaviour accordingly.
	 * 
	 * @param dialogState
	 *            int The state the dialog should be opened in.
	 */
	public String[] open() {
		createTextWidgets();
		createScopeButtons(); // specify the scope
		createControlButtons();
		shell.pack();
		shell.open();
		Display display = shell.getDisplay();
		while (!shell.isDisposed()) {
			if (!display.readAndDispatch())
				display.sleep();
		}

		return getValues();
	}
}
