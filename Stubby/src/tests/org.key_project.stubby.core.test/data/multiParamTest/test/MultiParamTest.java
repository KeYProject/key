import java.awt.Color;

public class MultiParamTest extends Color {
	public MultiParamTest() {
		super(0, false);
		getColor("");
		getColor("", 0);
		getHSBColor(0.0f, 0.0f, 0.0f);	
	}
}