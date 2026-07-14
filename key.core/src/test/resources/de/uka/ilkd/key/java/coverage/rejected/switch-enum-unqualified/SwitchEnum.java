enum Color { RED, GREEN, BLUE }

public class SwitchEnum {
    int f(Color c) {
        switch (c) {
            case RED:   return 1;
            case GREEN: return 2;
            default:    return 3;
        }
    }
}
