package wrapper;
import javax.swing.JComponent;

public class Wrapper<T extends JComponent> {
	private T t;

	public Wrapper(T t) {
		super();
		this.t = t;
	}

	public T getT() {
		return t;
	}
}
