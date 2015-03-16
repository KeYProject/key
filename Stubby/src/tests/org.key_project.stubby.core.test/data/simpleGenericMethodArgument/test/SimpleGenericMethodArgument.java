import java.io.Serializable;

public class SimpleGenericMethodArgument {
	public static <T extends Serializable, X> X magic(T t) {
		return null;
	}
}
