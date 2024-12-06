public class SimpleTest {
    public int example(int x) {
        int y = 0;
        if (x > 10) {
            y = 1;
            if (x > 20) {
                return y + 2;
            } else {
                y = 3;
            }
        } else {
            y = 4;
        }
        return y;
    }
}