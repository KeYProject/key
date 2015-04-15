import javax.swing.JButton;

import wrapper.Wrapper;

public class Main {
	public static void main(String[] args) {
		Wrapper<JButton> w = new Wrapper<JButton>(new JButton());
		System.out.println(w.getT().isDefaultButton());
	}
}
