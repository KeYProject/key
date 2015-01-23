package de.uka.ilkd.key.gui.testgen;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.ScrollPaneConstants;
import javax.swing.WindowConstants;
import javax.swing.text.DefaultCaret;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.smt.testgen.TestGenerationLog;

@SuppressWarnings("serial")
public class TGInfoDialog extends JDialog implements TestGenerationLog {
	private final JTextArea textArea;
	private final JButton stopButton;
	private final JButton exitButton;
	private final JButton startButton;
	
	private TGWorker worker;

	public TGInfoDialog() {
		super(MainWindow.getInstance());
		textArea = new JTextArea();
		setLayout(new BorderLayout());
		final JScrollPane scrollpane = new JScrollPane(textArea);
		scrollpane
		        .setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		scrollpane
		        .setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS);
		final DefaultCaret caret = (DefaultCaret) textArea.getCaret();
		caret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);
		
		
		
		stopButton = new JButton(new AbstractAction("Stop") {
			@Override
			public void actionPerformed(ActionEvent e) {
				MainWindow.getInstance().getMediator().stopAutoMode();
				exitButton.setEnabled(true);
			}
		});
		exitButton = new JButton(new AbstractAction("Exit") {
			@Override
			public void actionPerformed(ActionEvent e) {
				TGInfoDialog.this.dispose();
			}
		});
		startButton = new JButton(new AbstractAction("Start") {
			@Override
			public void actionPerformed(ActionEvent e) {
				KeYMediator mediator = MainWindow.getInstance().getMediator();
				mediator.stopInterface(true);
				mediator.setInteractive(false);				
				worker = new TGWorker(TGInfoDialog.this);
				mediator.addInterruptedListener(worker);
				worker.execute();
			}
		});
		exitButton.setEnabled(false);
		final JPanel flowPanel = new JPanel(new FlowLayout());
		flowPanel.add(startButton);
		flowPanel.add(stopButton);
		flowPanel.add(exitButton);
		getContentPane().add(scrollpane, BorderLayout.CENTER);
		getContentPane().add(flowPanel, BorderLayout.SOUTH);
		getContentPane().add(new TestGenOptionsPanel(), BorderLayout.EAST);
		setModal(false);
		// this.pack();
		setTitle("Test Suite Generation");
		this.setSize(700, 300);
		setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
		setLocationRelativeTo(MainWindow.getInstance());
		setVisible(true);
	}

   @Override
	public void write(String t) {
		textArea.append(t);
	}

   @Override
	public void writeln(String line) {
		textArea.append(line + "\n");
	}

   @Override
   public void writeException(Throwable t) {
      t.printStackTrace();
      textArea.append("Error: " + t.getMessage());
   }

   @Override
   public void testGenerationCompleted() {
      exitButton.setEnabled(true);
   }
}
