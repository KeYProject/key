import javax.swing.JFrame;
import javax.swing.JRootPane;

public class InnerThis {
	public static void main() {
		new JFrame() {
			public JRootPane inner() {
				JRootPane result = this.rootPane;
				return result;
			}
		};
	}
}