package org.key_project.key4eclipse.starter.ui.handler;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.awt.SWT_AWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.util.key.KeYUtil;

import de.uka.ilkd.key.util.removegenerics.Main;

/**
 * Handler that starts the KeY UI via {@link KeYUtil#openMainWindow()}.
 */
public class StartKeYHandler extends AbstractSaveExecutionHandler {
    /**
     * {@inheritDoc}
     */
    @Override
    protected Object doExecute(ExecutionEvent event) throws Exception {
        Shell shell = new Shell();
        shell.setText("SWT with Swing");
        shell.setLayout(new FillLayout());
        shell.setSize(200, 200);
        Composite swtAwtComponent = new Composite(shell, SWT.EMBEDDED);
        java.awt.Frame frame = SWT_AWT.new_Frame( swtAwtComponent );
        frame.setLayout(new BorderLayout());
        javax.swing.JPanel panel = new javax.swing.JPanel( );
        panel.setLayout(new BorderLayout());
        JButton button = new JButton("JButton");
        button.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                try {
                    KeYUtil.openMainWindow();
                }
                catch (Exception e1) {
                    e1.printStackTrace();
                }
            }
        });
        panel.add(button, BorderLayout.CENTER);
        frame.add(panel, BorderLayout.CENTER);
        frame.setVisible(true);
        shell.setVisible(true);
        
//        KeYUtil.openMainWindowAsync();
        return null;
    }
}
