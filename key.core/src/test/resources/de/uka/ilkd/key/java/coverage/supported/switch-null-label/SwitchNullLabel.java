public class SwitchNullLabel {
    int f(String s) {
        int r;
        switch (s) {
            case null: r = -1; break;
            case "x":  r = 1;  break;
            default:   r = 0;
        }
        return r;
    }
}
