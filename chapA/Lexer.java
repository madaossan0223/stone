package chapA;

import java.io.IOException;
import java.io.Reader;
import stone.CodeDialog;

/*
 * 手写 DFA(Deterministic Finite Automaton)
 * 等价于如下正则表达式:
 * \s*([0-9][0-9]*|[A-Za-z][A-Za-z0-9]*|=|==)
 * \s 表示空白符
 *
 * and the Automaton:
 *
 *     \s                 0-9
 *    +----+            +------+
 *    |    |            |      |
 *    +-  -+            +- ----+             A-Za-z0-9
 *     (1) ------------> ((2))             +-----------+
 *     | |                                 |           |
 *     | |                                 +-  --------+
 *     | +--------------------------------> ((3))
 *     |
 *     |  =             =
 *     +------> ((4)) ------> ((4))
 *
 * () 里面是开始状态, (()) 里面是接受/结束状态.
 */

public class Lexer {
    private Reader reader;
    private static final int EMPTY = -1;
    private int lastChar = EMPTY;

    public Lexer(Reader r) { reader = r; }

    private int getChar() throws IOException {
        if (lastChar == EMPTY)
            return reader.read();
        else {
            int c = lastChar;
            lastChar = EMPTY;
            return c;
        }
    }

    private void ungetChar(int c) { lastChar = c; }

    public String read() throws IOException {
        StringBuilder sb = new StringBuilder();
        int c;
        do {
            c = getChar();
        } while (isSpace(c));

        if (c < 0)
            return null; // end of text
        else if (isDigit(c)) {
            do {
                sb.append((char)c);
                c = getChar();
            } while (isDigit(c));
        }
        else if (isLetter(c)) {
            do {
                sb.append((char)c);
                c = getChar();
            } while (isLetter(c) || isDigit(c));
        }
        else if (c == '=') {
            c = getChar();
            if (c == '=')
                return "==";
            else {
                ungetChar(c);
                return "=";
            }
        }
        else
            throw new IOException();

        if (c >= 0)
            ungetChar(c);

        return sb.toString();
    }

    private static boolean isLetter(int c) {
        return 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z';
    }

    private static boolean isDigit(int c) {
        return '0' <= c && c <= '9';
    }

    private static boolean isSpace(int c) {
        return 0 <= c && c <= ' ';
    }

    public static void main(String[] args) throws Exception 
    {
        Lexer l = new Lexer(new CodeDialog());
        for (String s; (s = l.read()) != null; )
            System.out.println("-> " + s);
    }
}
