enum ColorQ { RED, GREEN, BLUE }

public class SwitchEnumQ {
    int f(ColorQ c) {
        switch (c) {
            case ColorQ.RED:   return 1;
            case ColorQ.GREEN: return 2;
            default:           return 3;
        }
    }
}
