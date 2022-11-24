import java.util.Scanner;

public class ConsoleView extends View {
    public ConsoleView(int[] boardSize) {
        super(boardSize);
    }

    @Override
    public void drawBoard(Board board) {
        String verticalSeparator = "|";
        System.out.println();
        for (int col = 0; col < this.boardSize[1]; col++) {
            System.out.printf("%s%d", verticalSeparator, col);
        }
        System.out.println(verticalSeparator);

        int[][] boardState = board.getState();
        for (int row = 0; row < this.boardSize[0]; row++) {
            for (int col = 0; col < this.boardSize[1]; col++) {
                char marker = ' ';
                if (boardState[row][col] == 1) {
                    marker = 'X';
                } else if (boardState[row][col] == 2) {
                    marker = 'O';
                }
                System.out.printf("%s%c", verticalSeparator, marker);
            }
            System.out.println(verticalSeparator);
        }
        System.out.println();

    }

    @Override
    public int getStep(int player) {
        System.out.printf("Player %d selects col: ", player);
        int col = 0;
        while (true) {
            Scanner inputScanner = new Scanner(System.in);
            if (inputScanner.hasNextInt()) {
                col = inputScanner.nextInt();
                break;
            }
        }

        return col;
    }
}
