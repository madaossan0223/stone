package stone;

import java.io.IOException;
import java.io.LineNumberReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Lexer {
    /*
     * 首先, 把 token 限定为 3 种, 标识符, 整形字面量, 字符串字面量
     * 由于只支持整形字面量, 这表明, stone 语言将只支持整数计算(当然这一点关系
     * 都没有, 因为真正任意精度的浮点运算可以通过字符串计算来模拟的^_^).
     *
     * 所以词法分析器的核心正则表达式的结构是这样:
     * \s*((//.*)|(pat1)|(pat2)|pat3)?
     *
     * 1. 起始的 \s 与空字符匹配, \s* 与 0 个及 0 个以上的空字符匹配.
     * 2. (//.*) 与注释匹配.
     * 3. pat1 是 [0-9]+, 与整型字面量匹配.
     * 4. pat2 是 "(\\"|\\\\|\\n|[^"])*", 与字符串字面量匹配. 从整体上看, pat2
     *    是一个 (pat)* 形式的模式, 即双引号内是一个与 pat 重复出现至少 0 次的
     *    结果匹配的字符串. 其中, 模式 pat 与 \" \\ \n 或除 " 之外任意一个字符
     *    匹配. 正则中反斜杠 \ 是用于转义的 meta, 因此在正则表达式中需要用 \\
     *    表示字符意义上的\. 再需要注意的是, java 语言的字符串字面量本身也将 \
     *    用于转义 meta, 也就是说, pat2 需要先经过 java 语言字符串字面量的转义
     *    规则才成为 "(\\"|\\\\|\\n|[^"])*".
     * 5. pat3 匹配标识符和运算符. 标识符和运算符没有区分. 由于 | 是正则表达式
     *    meta, 所以 \|\| 表示 ||. \p{Punct} 表示与任何符号字符匹配.
     *
     * 执行词法分析时, 语言处理器将逐行读取源码, 从各行开头起检查内容是否与该
     * 正则表达式匹配, 并在检查完成后获取与正则表达式括号内的模式匹配的字符串.
     *
     * 比如, 左起第一个括号对应的字符串与该括号内对应的模式匹配, 不包括字符串
     * 头部的空白字符. 如果匹配的字符串是一句注释, 则对应于左起第2个左括号, 从
     * 第3个左括号起对应的都是null. 如果匹配的字符串是一个整型字面量, 则对应于
     * 左起第3个左括号, 第2个和第4个左括号与 null 对应. 以此类推.
     */
    public static String regexPat
        = "\\s*((//.*)|([0-9]+)|(\"(\\\\\"|\\\\\\\\|\\\\n|[^\"])*\")"
          + "|[A-Z_a-z][A-Z_a-z0-9]*|==|<=|>=|&&|\\|\\||\\p{Punct})?";
    private Pattern pattern = Pattern.compile(regexPat);
    private ArrayList<Token> queue = new ArrayList<Token>();
    private boolean hasMore;
    private LineNumberReader reader;

    /* 构造器, 初始化 reader. */
    public Lexer(Reader r) {
        hasMore = true;
        reader = new LineNumberReader(r);
    }

    /* 
     * 主方法, 获取剩余源码首 token. 这个方法是不在意行的区分的, 因为整个程序
     * 就是一个长字符串
     */
    public Token read() throws ParseException {
        if (fillQueue(0))
            return queue.remove(0);
        else
            return Token.EOF;
    }

    /* 主方法, 获取剩余源码第 i 个 token. 同样, 不 care 源码行 */
    public Token peek(int i) throws ParseException {
        if (fillQueue(i))
            return queue.get(i);
        else
            return Token.EOF;
    }

    /* 其实是调用 readLine 啦, 但是要判断剩下还有源码行没 */
    private boolean fillQueue(int i) throws ParseException {
        while (i >= queue.size())
            if (hasMore)
                readLine();
            else
                return false;
        return true;
    }

    /* 词法扫描器, 程序读取引擎 ^_^ */
    protected void readLine() throws ParseException {
        String line;
        try {
            line = reader.readLine();
        } catch (IOException e) {
            throw new ParseException(e);
        }
        if (line == null) {
            hasMore = false;
            return;
        }

        /* 获取行号. 行号将存储于 token 中 */
        int lineNo = reader.getLineNumber();

        /*
         * pattern 已经编译过, 我们只需要应用 matcher. 这正是正则库的黑魔法所在
         * 如果没有正则库, 那么你需要自己写正则库, 自己写正则库, 意味着你得去看
         * 确定型/非确定型有限状态自动机理论先^_^.
         */
        Matcher matcher = pattern.matcher(line);
        matcher.useTransparentBounds(true).useAnchoringBounds(false);

        int pos = 0;
        int endPos = line.length();
        while (pos < endPos) {
            /* 指定 matcher 需要 match 的范围 */
            matcher.region(pos, endPos);

            /* 
             * 每次 lookingAt, 则匹配一个 regexPat. 注意, regexPat 只匹配一个
             * token, 所以才需要 while
             */
            if (matcher.lookingAt()) {
                addToken(lineNo, matcher);
                pos = matcher.end();
            } else {
                throw new ParseException("bad token at line " + lineNo);
            }
        }

        /* 正则匹配完一行后, 最后一个字符一定是 EOL. regexPat 并不匹配 \n. */
        queue.add(new IdToken(lineNo, Token.EOL));
    }

    /* 词法扫描器的核心方法. 获得 token 加入 queue 啦 */
    protected void addToken(int lineNo, Matcher matcher) {
        String m = matcher.group(1);
        if (m != null) // if not a space
            if (matcher.group(2) == null) { // if not a comment
                Token token;
                if (matcher.group(3) != null)
                    token = new NumToken(lineNo, Integer.parseInt(m));
                else if (matcher.group(4) != null)
                    token = new StrToken(lineNo, toStringLiteral(m));
                else
                    token = new IdToken(lineNo, m);
                queue.add(token);
            }
    }

    protected String toStringLiteral(String s) {
        StringBuilder sb = new StringBuilder();
        int len = s.length() - 1;
        for (int i = 1; i < len; i++) {
            char c = s.charAt(i);
            if (c == '\\' && i + 1 < len) {
                int c2 = s.charAt(i + 1);
                if (c2 == '"' || c2 == '\\')
                    c = s.charAt(++i);
                else if (c2 == 'n') {
                    ++i;
                    c = '\n';
                }
            }
            sb.append(c);
        }
        return sb.toString();
    }

    protected static class NumToken extends Token {
        private int value;

        protected NumToken(int line, int v) {
            super(line);
            value = v;
        }
        public boolean isNumber() { return true; }
        public String getText() { return Integer.toString(value); }
        public int getNumber() { return value; }
    }

    protected static class IdToken extends Token {
        private String text;

        protected IdToken(int line, String id) {
            super(line);
            text = id;
        }
        public boolean isIdentifier() { return true; }
        public String getText() { return text; }
    }

    protected static class StrToken extends Token {
        private String literal;

        StrToken(int line, String str) {
            super(line);
            literal = str;
        }
        public boolean isString() { return true; }
        public String getText() { return literal; }
    }
}
