package sourcerer.view;

import java.awt.CardLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ModelElement;
import recoder.NamedModelElement;
import recoder.abstraction.ClassType;
import recoder.abstraction.Field;
import recoder.abstraction.Member;
import recoder.abstraction.Method;
import recoder.abstraction.Variable;
import recoder.bytecode.ClassFile;
import recoder.bytecode.FieldInfo;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.declaration.VariableSpecification;
import recoder.service.ConstantEvaluator;
import recoder.util.ProgressEvent;
import recoder.util.ProgressListener;
import sourcerer.DefaultSelectionModel;
import sourcerer.SelectionModel;
import sourcerer.util.RecoderUtils;
import sourcerer.util.SwingUtils;

public class StatusBar extends JPanel implements SelectionView, ProgressListener {

	JProgressBar progressBar;

	MemoryDisplay memory;

	JLabel selected;

	JPanel cardPanel;

	CardLayout cardLayout;

	SelectionModel model;

	CrossReferenceServiceConfiguration config;

	final static javax.swing.border.Border BORDER = BorderFactory.createCompoundBorder(BorderFactory.createEmptyBorder(
			2, 2, 2, 2), BorderFactory.createCompoundBorder(SwingUtils.createThinLoweredBevelBorder(), BorderFactory
			.createEmptyBorder(0, 2, 0, 2)));

	public StatusBar(CrossReferenceServiceConfiguration config, SelectionModel model) {
		super(new GridBagLayout());
		this.config = config;
		GridBagConstraints gbc = new GridBagConstraints();
		selected = new JLabel();
		selected.setForeground(getForeground());
		selected.setBorder(BORDER);
		progressBar = new JProgressBar();
		progressBar.setStringPainted(true);
		progressBar.setString("");
		progressBar.setFont(progressBar.getFont().deriveFont(9f));
		progressBar.setBorder(BORDER);
		cardPanel = new JPanel(cardLayout = new CardLayout());
		cardPanel.add(selected, "Element");
		cardPanel.add(progressBar, "Progress");

		gbc.gridx = 0;
		gbc.gridy = 0;
		gbc.fill = GridBagConstraints.HORIZONTAL;
		gbc.gridwidth = 3;
		gbc.weightx = 1.0;
		gbc.anchor = GridBagConstraints.NORTHWEST;
		add(cardPanel, gbc);
		memory = new MemoryDisplay();
		memory.setForeground(getForeground());
		memory.setBorder(BORDER);
		gbc.gridx = 3;
		gbc.gridy = 0;
		gbc.gridwidth = 1;
		gbc.weightx = 0.0;
		add(memory, gbc);
		setModel(model);
	}

	public JLabel getSelectionLabel() {
		return selected;
	}

	public SelectionModel getModel() {
		return model;
	}

	public void setModel(SelectionModel model) {
		if (this.model != model) {
			if (this.model != null) {
				this.model.removeChangeListener(changeListener);
			}
			if (model == null) {
				model = new DefaultSelectionModel();
			}
			model.addChangeListener(changeListener);
			this.model = model;
			updateView();
		}
	}

	public void modelUpdated(boolean selectionRemoved) {
		updateView();
	}

	protected final ChangeListener changeListener = new ChangeListener() {
		public void stateChanged(ChangeEvent e) {
			updateView();
		}
	};

	void updateView() {
		if (model == null) {
			selected.setText("");
		} else {
			ModelElement m = model.getSelectedElement();
			if (m == null) {
				selected.setText("No element selected");
				return;
			}
			StringBuffer text = new StringBuffer();
			if ((m instanceof Member) || (m instanceof Variable)) {
				if (m instanceof Member) {
					Member mb = (Member) m;
					if (mb.isPublic()) {
						text.append("public ");
					} else if (mb.isProtected()) {
						text.append("protected ");
					} else if (mb.isPrivate()) {
						text.append("private ");
					}
					if (mb.isStatic()) {
						text.append("static ");
					} else if (mb instanceof Method) {
						if (((Method) mb).isAbstract()) {
							text.append("abstract ");
						}
					} else if (mb instanceof ClassType) {
						if ((mb instanceof ClassFile) && ((ClassType) mb).isOrdinaryInterface()) {
							text.append("interface ");
						} else if (((ClassType) mb).isAbstract()) {
							text.append("abstract ");
						} else if ((mb instanceof ClassFile) && ((ClassType) mb).isEnumType()) {
							text.append("enum ");
						} else if ((mb instanceof ClassFile) && ((ClassType) mb).isAnnotationType()) {
							text.append("annotation ");
						}
					}
					if (mb.isFinal()) {
						text.append("final ");
					}
					if (mb.isStrictFp()) {
						text.append("strictfp ");
					}
					if (mb instanceof Method) {
						if (((Method) mb).isNative()) {
							text.append("native ");
						}
						if (((Method) mb).isSynchronized()) {
							text.append("synchronized ");
						}
					}
				}
				if ((m instanceof Variable) && !(m instanceof Field)) {
					if (((Variable) m).isFinal()) {
						text.append("final ");
					}
				}
			}
			String name = m.getClass().getName();
			text.append(name.substring(name.lastIndexOf('.') + 1));
			if (m instanceof CompilationUnit) {
				m = ((CompilationUnit) m).getPrimaryTypeDeclaration();
			}
			if (m instanceof NamedModelElement) {
				text.append(" \"");
				text.append(RecoderUtils.getNonTrivialName((NamedModelElement) m));
				text.append("\"");
			} else if (m instanceof Identifier) {
				text.append(" \"");
				text.append(((Identifier) m).getText());
				text.append("\"");
			}

			String constantValue = null;
			Expression expr = null;
			if (m instanceof FieldInfo) {
				constantValue = ((FieldInfo) m).getConstantValue();
			} else if (m instanceof VariableSpecification) {
				expr = ((VariableSpecification) m).getInitializer();
			} else if (m instanceof Expression) {
				expr = (Expression) m;
			}
			if (expr != null) {
				ConstantEvaluator.EvaluationResult evr = new ConstantEvaluator.EvaluationResult();
				if (config.getConstantEvaluator().isCompileTimeConstant(expr, evr)) {
					constantValue = evr.toString();
				}
			}
			if (constantValue != null) {
				text.append(" (constant value ");
				text.append(constantValue);
				text.append(")");
			}

			selected.setText(text.toString());

		}
	}

	public void workProgressed(ProgressEvent pe) {
		int max = pe.getWorkToDoCount();
		int val = pe.getWorkDoneCount();
		String msg = "";
		if (val == max) {
			val = 0;
			cardLayout.show(cardPanel, "Element");
		} else {
			cardLayout.show(cardPanel, "Progress");
			Object state = pe.getState();
			if (state != null) {
				msg = state.toString();
			}
			if (val > max) {
				max = val;
				// val = 0;
			}
		}
		progressBar.setValue(val);
		progressBar.setMaximum(max);
		progressBar.setString(msg);
	}

}
