package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Container;
import java.awt.Dialog.ModalityType;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.List;
import java.util.Observable;
import java.util.Observer;
import java.util.concurrent.CancellationException;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.SwingWorker;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;

import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.util.Debug;

public class ProofScriptWorker extends SwingWorker<Object, Object> implements InterruptListener {

    private final KeYMediator mediator;
    private final File file;
    private JDialog monitor;
    private JTextArea logArea;

    private final Observer observer = new Observer() {
        @Override
        public void update(Observable o, Object arg) {
            publish(arg);
        }
    };

    public ProofScriptWorker(KeYMediator mediator, File file) {
        this.mediator = mediator;
        this.file = file;
    }

    @Override
    protected Object doInBackground() throws Exception {
        try {
            ProofScriptEngine engine = new ProofScriptEngine(file);
            engine.setCommandMonitor(observer);
            engine.execute(mediator.getUI(), mediator.getSelectedProof());
        } catch(InterruptedException ex) {
            Debug.out("Proof macro has been interrupted:");
            Debug.out(ex);
        }
        return null;
    }

    private void makeDialog() {
        if(monitor != null) {
            logArea.setText("Running script from file '" + file + "':\n");
            return;
        }

        JDialog dlg = new JDialog(MainWindow.getInstance(), "Running Script ...",
                ModalityType.MODELESS);
        Container cp = dlg.getContentPane();
        logArea = new JTextArea();
        logArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
        logArea.setEditable(false);
        logArea.setText("Running script from file '" + file + "':\n");
        cp.add(new JScrollPane(logArea), BorderLayout.CENTER);

        JButton cancel = new JButton("Cancel");
        cancel.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                interruptionPerformed();
            }
        });
        JPanel panel = new JPanel(new FlowLayout());
        panel.add(cancel);
        cp.add(panel, BorderLayout.SOUTH);

        dlg.setSize(400, 400);
        dlg.setLocationRelativeTo(MainWindow.getInstance());

        this.monitor = dlg;
    }

    @Override
    protected void process(List<Object> chunks) {
        Document doc = logArea.getDocument();
        for (Object chunk : chunks) {
            try {
            doc.insertString(doc.getLength(), "\n---\nExecuting: " + chunk, null);
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
        }
    }

    /*
     * initiate the GUI stuff and relay to superclass
     */
    public void init() {
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(this);
        makeDialog();
        monitor.setVisible(true);
    }

    /*
     * finalise the GUI stuff
     */
    @Override
    public void done() {
        monitor.setVisible(false);

        try {
            get();
        } catch(CancellationException ex) {
            System.err.println("Scripting was cancelled.");
            Debug.printStackTrace(ex);
        } catch (Throwable ex) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), ex);
        }

        mediator.setInteractive(true);
        mediator.startInterface(true);
        mediator.removeInterruptedListener(this);
    }

    @Override
    public void interruptionPerformed() {
        // just notify the thread that the button has been pressed
        cancel(true);
    }

}
