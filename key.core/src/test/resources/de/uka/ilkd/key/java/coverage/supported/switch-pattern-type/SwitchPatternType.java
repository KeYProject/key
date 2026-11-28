public class SwitchPatternType {
    int f(Object o) {
        int r;
        switch (o) {
            case Integer i: r = i.intValue(); break;
            default: r = 0;
        }
        return r;
    }
}
