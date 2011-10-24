package de.uka.ilkd.key.gui.actions;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.FileInputStream;
import java.io.IOException;
import java.net.URL;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.KeYResourceManager;

public class LicenseAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -5859545563375095225L;

    public LicenseAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("License");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        showLicense();
    }

    public void showLicense() {
        
        URL lic = 
            KeYResourceManager.getManager().getResourceFile(MainWindow.class,
            "LICENSE.TXT"); 
        StringBuffer sb=new StringBuffer();
        try {
            FileInputStream inp=new FileInputStream(lic.getFile());
            while (inp.available()>0) sb.append((char)inp.read());	   
        } catch (IOException ioe) {
            System.out.println("License file cannot be loaded or is missing: \n"+
                    Main.COPYRIGHT+"\nKeY is protected by the "
                    +"GNU General Public License");
            sb=new StringBuffer(Main.COPYRIGHT+"\nKeY is protected by the "
                    +"GNU General Public License");
        } 
        String s=sb.toString();
        JScrollPane scroll = new JScrollPane();
        JTextArea text = new JTextArea(s,20,40);
        text.setEditable(false);
        text.setCaretPosition(0);
        scroll.setViewportView(text);
        JFrame fr = new JFrame("KeY License");
        fr.getContentPane().setLayout(new BorderLayout());
        fr.getContentPane().add(scroll,BorderLayout.CENTER);
        JButton ok = new JButton("OK");
        ok.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {		   
                ((JFrame)((JButton)e.getSource())
                        .getTopLevelAncestor()).dispose();
            }});
        fr.getContentPane().add(ok, BorderLayout.SOUTH);
        fr.setSize(600,900);
        fr.getContentPane().add(scroll);
        fr.setVisible(true);
    }
    
}
