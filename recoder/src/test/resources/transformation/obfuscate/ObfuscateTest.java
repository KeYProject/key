import javax.swing.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class ObfuscateTest extends JApplet {
    JLabel opLabel1 = new JLabel("Operand 1");
    JLabel opLabel2 = new JLabel("Operand 2");
    JLabel ergebnisLabel = new JLabel("Ergebnis: ");

    JTextField operand1, operand2, ergebnis;
    JButton add, sub;
    JPanel mitte, unten;

    public void init() {
        mitte = new JPanel();
        unten = new JPanel();
    opLabel1 = new JLabel (new ImageIcon(ObfuscateTest.class.getClassLoader().getResource("ibrahimface.gif")));
        mitte.add(opLabel1);
        mitte.add(operand1 = new JTextField("0", 10));
        mitte.add(opLabel2);
        mitte.add(operand2 = new JTextField("0", 10));
        mitte.add(ergebnisLabel);
        mitte.add(ergebnis = new JTextField("0", 10));

        add = new JButton("addieren");
        /** Beginn relevanter Quelltextteil */
        add.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                add(operand1.getText(), operand2.getText());
            }
        });
        sub = new JButton("subtrahieren");
        sub.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                sub(operand1.getText(), operand2.getText());
            }
        });
        /** Ende relevanter Quelltextteil */

        unten.add(add);
        unten.add(sub);

        getContentPane().add(mitte, BorderLayout.CENTER);
        getContentPane().add(unten, BorderLayout.SOUTH);
    }

    /**
     * Methoden add(...), sub(...) sollen auch abgefragt werden
     */
    public void add(String a, String b) {
        double Op1 = Double.parseDouble(a);
        double Op2 = Double.parseDouble(b);

        ergebnis.setText("" + (Op1 + Op2));
    }

    public void sub(String a, String b) {
        double Op1 = Double.parseDouble(a);
        double Op2 = Double.parseDouble(b);

        ergebnis.setText("" + (Op1 - Op2));
    }




/**
  This following code is not for teaching purpose, please ignore!
*/
   public static void main (String args []) {
         //new AppletContainerDialog (ObfuscateTest.class).show ();
    }

}
