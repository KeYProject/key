
import javax.swing.JButton;

import wrapper.Wrapper;

public class Main {
        public static void main(String[] args) {
                Wrapper w =  new Wrapper(new JButton());
                System.out.println(((javax.swing.JButton)w.getT()).isDefaultButton());
    }
}
