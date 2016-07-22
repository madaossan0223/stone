package stone;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ArrayList;
import java.lang.reflect.Method;
import java.lang.reflect.Constructor;
import stone.ast.ASTree;
import stone.ast.ASTLeaf;
import stone.ast.ASTList;

/*
 * 1. Parser 类中的嵌套子类继承树
 *
 *                   +=========+
 *                   | Element |
 *                   |=========+
 *                   | parse   |
 *                   | match   |
 *                   +=========+
 *                        ^
 *      +-----------------+-----------------------+--------+----------+---------+
 *      |                 |                       |        |          |         |
 * +========+         +======+                +======+ +========+ +========+ +======+
 * | AToken |         | Expr |                | Leaf | | Repeat | | OrTree | | Tree |
 * +========+         +======+                +======+ +========+ +========+ +======+
 *      ^                                         ^
 *      |                                         |
 *      +-------------+---------------+        +======+
 *      |             |               |        | Skip |
 * +=========+    +==========+    +==========+ +======+
 * | IdToken |    | NumToken |    | StrToken |
 * +=========+    +==========+    +==========+
 *
 * 每个嵌套子类对象用于表现其对应的简单语法规则.
 *
 *
 * 2. Parser 类自身结构:
 *
 * 除上述自 Element 形成继承树的嵌套类之外,
 * Parser 类内部还有 Precedence Operators 两个用来表达算符优先
 * 语法分析的类; 以及一个抽象工厂类 Factory(用于创建AST节点).
 *
 * +=============================================================+
 * | List<Element> elements;                                     |
 * | Factory factory;                                            |
 * +-------------------------------------------------------------+
 * | Parser(Class<? extends ASTree> clazz);                      |
 * | Parser(Parser p);                                           |
 * | ASTree     parse(Lexer lexer);                              |
 * | boolean    match(Lexer lexer);                              |
 * | Parser     rule();                                          |
 * | Parser     rule(Class<? extends ASTree> clazz);             |
 * | Parser     reset();                                         |
 * | Parser     reset(Class<? extends ASTree> clazz);            |
 * | Parser     number();                                        |
 * | Parser     number(Class<? extends ASTLeaf> clazz);          |
 * | Parser     identifier(HashSet<String> reserved);            |
 * | Parser     identifier(Class<? extends ASTLeaf> clazz,       |
 * |                       HashSet<String> reserved);            |
 * | Parser     string();                                        |
 * | Parser     string(Class<? extends ASTLeaf> clazz);          |
 * | Parser     token(String... pat);                            |
 * | Parser     sep(String... pat);                              |
 * | Parser     ast(Parser p);                                   |
 * | Parser     or(Parser... p);                                 |
 * | Parser     maybe(Parser p);                                 |
 * | Parser     option(Parser p);                                |
 * | Parser     repeat(Parser p);                                |
 * | Parser     expression(Parser subexp, Operators operators);  |
 * | Parser     expression(Class<? extends ASTree> clazz,        |
 * |                       Parser subexp, Operators operators);  |
 * | Parser     insertChoice(Parser p);                          |
 * +=============================================================+
 *
 * 我们考察这个类的方法, 可以发现, 除 parse 和 match 之外, 其余的方法全部返回
 * Parser 对象. 
 *
 * 这某种程度上可看作是对 FP(Functional Programming) 编程范式的一种模拟(FP 
 * 语言中的函数可以返回函数, 可以以函数作为参数, 从而操纵函数的函数被称之为高阶
 * 函数. 如果高阶函数接受若干函数作为参数, 并返回函数, 这样的高阶函数就可以称为
 * 组合子(Combinator).
 * Y-Combinator(Fixed-point combinator)是一种著名的组合子, 用于表述
 * lambda calulus 的递归计算(lambda calulus 的函数是匿名的). 其定义如下:
 * ;; represented by lambda calculus:
 * \f.(\x.f(x x))(\x.f(x x)) 
 * ;; and represented by scheme:
 * (define Y
 *     (lambda (f)
 *         ((lambda (x)
 *              (f (lambda (arg) ((x x) arg))))
 *          (lambda (x)
 *              (f (lambda (arg) ((x x) arg)))))))
 *
 * 在 FP 中, 将多个能对简单语法执行语法分析(parsing)的函数进行组合后, 我们就能
 * 获得能够对更复杂的语法进行分析的函数(组合子). 即解析组合子.
 * 
 * Parser 类中, 除 parse 和 match 之外的方法, 总是返回 Parser 对象, 而且其中
 * 某些函数也可以接收 Parser 对象作为参数, 这样的函数其实和高阶函数有类似的
 * 地方, 这意味着我们可以通过这些函数组合对象.
 * 将多个能对简单语法执行语法分析的 Parser 对象进行组合后, 我们就能获得能够对更
 * 复杂的语法进行分析的 Parser 对象. 
 * (...哎, 干嘛要扯淡这些...).
 *
 * 如 1 所描述的 Parser 类中嵌套子类的继承树, 这些嵌套子类用于表现 Parser 对象
 * 需要处理的语法规则模式. 
 * 在将语法规则转换为 Parser 对象时, 会调用 number 或 ast 等方法来构造模式. 
 * 这些方法将创建 Parser 嵌套子类对象, 并将它们添加到 Parser 对象的 elements
 * 字段指向的 ArrayList 中. 比如, ast 方法将创建一个 Tree 对象, 并将其添加至
 * ArrayList 中.
 *
 * parse 方法将根据构造的模式执行语法分析. 它主要采用 LL(1) 语法分析方式, 并
 * 根据需要, 部分使用了算符优先分析法(LR 的弱化 --> 弱化版本).
 * 注意Parser类的 parse 方法返回的是 ASTree 对象, 也就意味 parse 方法将会创建
 * 并返回相应的抽象语法树. 而 Parser 的嵌套子类的 parse 方法则是 void 方法,
 * 意味着嵌套子类的 parse 方法将调用 Parser 类的 parse 方法.
 *
 * 在 Parser 类的嵌套子类提供的 parse 方法中, 最重要的是 OrTree 类的 parse
 * 方法. Parser 类的 or 方法将使用 OrTree 来实现 "或" 运算逻辑. 它与语法模式的
 * 可视化图形形式中的分支箭头对应. 不过该方法需要确定箭头的走向.
 * 如有必要, LL 语法分析将预读单词, 以确定箭头的走向. 也就是说, 语法分析器将
 * 预先调查之后将接收什么单词, 并选择能成功执行语法分析的路径. 该操作由 Parser
 * 类及其嵌套子类的 match 方法执行.
 *
 * 由于 Parser 基本上是 LL(1), 并且在实现上, OrTree 仅会选择第一个 match 的分支
 * 执行, 所以对语法的要求是, 必须通过一次预读就可以确定分支选择. 因此, 此 Parser
 * 的 or 方法并不能完全表达 BNF 的 |, 也就是不符合前述要求的语法是不能被分析的.
 *
 * 例如, 如下是 factor 的语法模式的可视化形式:
 *        +===+      +============+      +===+
 *  +---> | ( | ---> | expression | ---> | ) |---+
 *  |     +===+      +============+      +===+   |
 *  |                                            |
 *  |                  +========+                |
 * -+----------------> | NUMBER | ---------------+--->
 *                     +========+
 * 使用 Parser 类, 即可根据该模式构建组合 Parser 类对象:
 * Parser factor = rule().or(rule().sep("(").ast(expr).sep(")"),
 *                           rule().number());
 *
 * 组合对象:                                                  +==========+
 * (factor 的 elements 列表里面是 OrTree,                 +-> |exp:Parser| ->...
 *  而 OrTree 对象中的 parser[0] 的 elements              |   +==========+
 *  则是 Skip, Tree, Skip)           elements             |
 *                             +=======+    +=====+    +=====+    +=====+
 * +=======+               +-> |:Parser| -> |:Skip| -> |:Tree| -> |:Skip|
 * |factor:|    +=======+  |   +=======+    +=====+    +=====+    +=====+
 * +-------+ -> |:OrTree| -+               tokens="("            tokens=")"
 * |Parser |    +=======+  |         elements
 * +=======+               |   +=======+    +=========+
 *         elements        +-> |:Parser| -> |:NumToken|
 *                             +=======+    +=========+
 */
public class Parser {
    /* 抽象语法树中的任意节点, 都可以使用 Element parse 其语法规则 */
    protected static abstract class Element {
        protected abstract void parse(Lexer lexer, List<ASTree> res)
            throws ParseException;
        protected abstract boolean match(Lexer lexer) throws ParseException;
    }

    /*
     * Tree 用于 parse 抽象语法树中任意一颗子树并得到其 ASTree. 见 ast.
     * 正因如此, 它的 parse 方法只是简单地调用 Parser.parse, Parser.parse 返回
     * 根据(子表达式 or something other)语法规则遍历后的 ASTree 对象(也就是
     * ASTree 的根节点), 然后将此对象加入 ASTree List 中即可.
     */
    protected static class Tree extends Element {
        protected Parser parser;
        protected Tree(Parser p) { parser = p; }

        protected void parse(Lexer lexer, List<ASTree> res)
            throws ParseException
        {
            res.add(parser.parse(lexer));
        }

        protected boolean match(Lexer lexer) throws ParseException {
            return parser.match(lexer);
        }
    }

    /*
     * 见 or, maybe, insertChoice
     * OrTree 用于 parse (语法规则的可视化形式)中的分支选择.
     */
    protected static class OrTree extends Element {
        /* 每个分支都需要一个 Parser, 所以这里是 parsers. */
        protected Parser[] parsers;
        protected OrTree(Parser[] p) { parsers = p; }

        /* 先选择分支, 然后直接 parse. 呐, 如果这里加回溯处理的话, 会更强吗? */
        protected void parse(Lexer lexer, List<ASTree> res)
            throws ParseException
        {
            Parser p = choose(lexer);
            if (p == null)
                throw new ParseException(lexer.peek(0));
            else
                res.add(p.parse(lexer));
        }

        protected boolean match(Lexer lexer) throws ParseException {
            return choose(lexer) != null;
        }

        /* 有一个分支 match 吗? */
        protected Parser choose(Lexer lexer) throws ParseException {
            for (Parser p: parsers)
                if (p.match(lexer))
                    return p;

            return null;
        }

        /* 加入分支 parser. */
        protected void insert(Parser p) {
            Parser[] newParsers = new Parser[parsers.length + 1];
            newParsers[0] = p;
            System.arraycopy(parsers, 0, newParsers, 1, parsers.length);
            parsers = newParsers;
        }
    }

    /* Repeat 重复添加非终结符, 见 repeat, option */
    protected static class Repeat extends Element {
        protected Parser parser;
        protected boolean onlyOnce;
        protected Repeat(Parser p, boolean once) { parser = p; onlyOnce = once; }

        protected void parse(Lexer lexer, List<ASTree> res)
            throws ParseException
        {
            while (parser.match(lexer)) {
                ASTree t = parser.parse(lexer);
                /* 所添加的非终结符不能是 ASTList 类, 要注意这一点 */
                if (t.getClass() != ASTList.class || t.numChildren() > 0)
                    res.add(t);
                if (onlyOnce)
                    break;
            }
        }

        protected boolean match(Lexer lexer) throws ParseException {
            return parser.match(lexer);
        }
    }

    /* 对 Token 的遍历. 见 number, identifier, string */
    protected static abstract class AToken extends Element {
        protected Factory factory;
        protected AToken(Class<? extends ASTLeaf> type) {
            if (type == null)
                type = ASTLeaf.class;
            /*
             * clazz == ASTLeaf.class, argType = Token.class
             * ASTLeaf 由 token 构建.
             */
            factory = Factory.get(type, Token.class);
        }

        protected void parse(Lexer lexer, List<ASTree> res)
            throws ParseException
        {
            Token t = lexer.read();
            if (test(t)) {
                /* 嗯, 这里通过 factory 创建 AST node */
                ASTree leaf = factory.make(t);
                res.add(leaf);
            }
            else
                throw new ParseException(t);
        }

        protected boolean match(Lexer lexer) throws ParseException {
            return test(lexer.peek(0));
        }

        /* 由子类重写 */
        protected abstract boolean test(Token t);
    }

    /* 
     * IdToken 比较特殊的地方, 因为 stone 词法分析器将把所有符号识别为标识符,
     * HashSet 中表明了不可被识别为变量名参与语法分析的符号. 不过有的不可识别
     * 为变量的标识符已经直接写进语法规则了(见 BasicParser).
     */
    protected static class IdToken extends AToken {
        HashSet<String> reserved;
        protected IdToken(Class<? extends ASTLeaf> type, HashSet<String> r) {
            super(type);
            reserved = r != null ? r : new HashSet<String>();
        }

        protected boolean test(Token t) {
            return t.isIdentifier() && !reserved.contains(t.getText());
        }
    }

    protected static class NumToken extends AToken {
        protected NumToken(Class<? extends ASTLeaf> type) { super(type); }
        protected boolean test(Token t) { return t.isNumber(); }
    }

    protected static class StrToken extends AToken {
        protected StrToken(Class<? extends ASTLeaf> type) { super(type); }
        protected boolean test(Token t) { return t.isString(); }
    }

    /* 见 token(方法) */
    protected static class Leaf extends Element {
        protected String[] tokens;
        protected Leaf(String[] pat) { tokens = pat; }

        protected void parse(Lexer lexer, List<ASTree> res)
            throws ParseException
        {
            Token t = lexer.read();
            if (t.isIdentifier())
                for (String token: tokens)
                    if (token.equals(t.getText())) {
                        find(res, t);
                        return;
                    }

             if (tokens.length > 0)
                 throw new ParseException(tokens[0] + " expected.", t);
             else
                 throw new ParseException(t);
        }

        protected void find(List<ASTree> res, Token t) {
            res.add(new ASTLeaf(t));
        }

        protected boolean match(Lexer lexer) throws ParseException {
            Token t = lexer.peek(0);
            if (t.isIdentifier())
                for (String token: tokens)
                    if (token.equals(t.getText()))
                        return true;

            return false;
        }
    }

    /* 见 sep */
    protected static class Skip extends Leaf {
        protected Skip(String[] t) { super(t); }
        protected void find(List<ASTree> res, Token t) { }
    }

    public static class Precedence {
        int value;
        boolean leftAssoc; // left associative
        public Precedence(int v, boolean a) {
            value = v; leftAssoc = a;
        }
    }

    public static class Operators extends HashMap<String, Precedence> {
        public static boolean LEFT = true;
        public static boolean RIGHT = false;

        public void add(String name, int prec, boolean leftAssoc) {
            put(name, new Precedence(prec, leftAssoc));
        }
    }

    /* 算符优先分析, 使用 shift-reduce parsing */
    protected static class Expr extends Element {
        protected Factory factory;
        protected Operators ops;
        protected Parser factor;

        protected Expr(Class<? extends ASTree> clazz, Parser exp,
                       Operators map)
        {
            factory = Factory.getForASTList(clazz);
            ops = map;
            factor = exp;
        }

        public void parse(Lexer lexer, List<ASTree> res) throws ParseException {
            ASTree right = factor.parse(lexer);
            Precedence prec;

            /* shift-reduce parsing. */
            while ((prec = nextOperator(lexer)) != null)
                right = doShift(lexer, right, prec.value);

            res.add(right);
        }

        private ASTree doShift(Lexer lexer, ASTree left, int prec)
            throws ParseException
        {
            ArrayList<ASTree> list = new ArrayList<ASTree>();
            list.add(left);
            list.add(new ASTLeaf(lexer.read()));
            ASTree right = factor.parse(lexer);
            Precedence next;

            /* the actual implemention of shift-reduce parsing. */
            while ((next = nextOperator(lexer)) != null
                   && rightIsExpr(prec, next))
               right = doShift(lexer, right, next.value);

            list.add(right);
            /* 嗯, 这里通过 factory.make 创建 AST node */
            return factory.make(list);
        }

        private Precedence nextOperator(Lexer lexer) throws ParseException {
            Token t = lexer.peek(0);
            if (t.isIdentifier())
                return ops.get(t.getText());
            else
                return null;
        } 

        private static boolean rightIsExpr(int prec, Precedence nextPrec) {
            if (nextPrec.leftAssoc)
                return prec < nextPrec.value;
            else
                return prec <= nextPrec.value;
        }

        protected boolean match(Lexer lexer) throws ParseException {
            return factor.match(lexer);
        }
    }

    /*
     * 据说, 简单工厂模式是酱紫的:
     *
     *               class B <----------------- class Factory
     *                 ^                        -------------
     *                 |                          :createBX
     *    +------------o----------+-----------+
     *    |            |          |           |          
     * class BA    class BS    class BM    class BD
     *
     * 工厂模式是酱紫的:
     *
     *               class B <--------------------------- class Factory
     *                 ^                                  -------------
     *                 |                                    :createBX
     *                 |                                       ^
     *    +------------o----------+-----------+                |
     *    |            |          |           |        +-------+------+-----+
     * class BA    class BS    class BM    class BD    |              |     |
     *    ^            ^                               |              |     ...
     *    |            |                               |              |
     *    +------------o--------------------- class FactoryBA         |
     *                 +-------------------------------------- class FactoryBS
     *
     * 抽象工厂模式是酱紫的:
     *
     *               IUser                              IFactory
     *                ^                                    ^
     *      +---------+---------+                +---------+--------+
     *      |                   |                |                  |
     * SqlserverUser        AccessUser    AccessFactory       SqlserverFactory
     *      ^                   ^         -------------       ----------------
     *      |                   |         :createUser         :createUser
     *      |                   |         :createDepartment   :createDepartment
     *      |                   +----------------+                  |
     *      +------------------------------------o------------------+
     *             IDepartment                   |                  |
     *                  ^                        |                  |
     *      +-----------+----------+             |                  |
     *      |                      |             |                  |
     * SqlserverDapartment  AccessDepartment     |                  |
     *      ^                      ^             |                  |
     *      |                      +-------------+                  |
     *      +-------------------------------------------------------+
     *
     * 那么请问, 下面这个 Factory 是上面哪一种? ^_^
     */
    public static final String factoryName = "create";
    protected static abstract class Factory {
        /* 
         * get / getForASTList 返回 Factory 对象
         * 同时在构造 Factory 对象时将 make0 重写(匿名类,继承自抽象类Factory)
         * 使用时调用所返回 Factory 对象的 make 方法
         * 这个实现还是比较巧妙的...
         */
        protected abstract ASTree make0(Object arg) throws Exception;

        /*
         * 也就是 Factory 的 create 操作了.
         * 作为 parser, parse 完语法规则, 需要创建的自然是抽象语法树节点.
         */
        protected ASTree make(Object arg) {
            try {
                return make0(arg);
            } catch (IllegalArgumentException e1) {
                throw e1;
            } catch (Exception e2) {
                throw new RuntimeException(e2); // this compiler is broken
            }
        }

        /*
         * 返回 Factory 对象, 所返回的对象用于创建 AST 的 root node.
         */
        protected static Factory getForASTList(Class<? extends ASTree> clazz) {
            Factory f = get(clazz, List.class);
            if (f == null) {
                f = new Factory() {
                    protected ASTree make0(Object arg) throws Exception {
                        List<ASTree> results = (List<ASTree>)arg;
                        if (results.size() == 1)
                            return results.get(0);
                        else
                            return new ASTList(results);
                    }
                };
            }

            return f;
        }

        /*
         * 返回 Factory 对象.
         * 不过, 所返回的 Factory 对象所属的类实际上是继承自 Factory 的匿名类,
         * 而且都重写了 make0 方法.
         * clazz 自然是 ASTree 及其子类(这个 Factory 是用来生产 ASTree 节点的)
         * argType 则是 clazz "create" 方法的参数所属类,
         *         或是 clazz 构造器的参数所属类.
         */
        protected static Factory get(Class<? extends ASTree> clazz,
                                     Class<?> argType)
        {
            if (clazz == null)
                return null;

            try {
                /*
                 * factoryName == "create", 比如见 ast/PrimaryExpr
                 * new Class<?>[] { argType } 是方法 "create" 的
                 * formal paraments 的Class数组, 数组中的元素代表参数的Class.
                 * 比如当 clazz == PrimaryExpr, 那么 m != null 成立.
                 * 否则抛出异常, 因为我们 catch 为空语句, 这样执行流就到下一个
                 * try block.
                 */
                final Method m = clazz.getMethod(factoryName,
                                                 new Class<?>[] { argType });
                return new Factory() {
                    protected ASTree make0(Object arg) throws Exception {
                        /*
                         * invoke 的第一个参数是 null, 表明 m 必然属于静态方法,
                         * 不需借助(clazz 的)实例运行.
                         * 这里 arg 自然就是 "create" 的 actual arguments 了.
                         */
                        return (ASTree)m.invoke(null, arg);
                    }
                };
            } catch (NoSuchMethodException e) { }

            try {
                /* 
                 * argType 是clazz类(Class的实例)的构造器的 formal parameter
                 * 所属的Class
                 */
                final Constructor<? extends ASTree> c
                    = clazz.getConstructor(argType);
                return new Factory() {
                    protected ASTree make0(Object arg) throws Exception {
                        /* arg 是clazz类的构造器 actual argument. */
                        return c.newInstance(arg);
                    }
                };
            } catch (NoSuchMethodException e) {
                throw new RuntimeException(e);
            }
        }
    }

    protected List<Element> elements;
    protected Factory factory;

    /* 构造器, 构造新 Parser, 抽象语法树的根节点类为 clazz */
    public Parser(Class<? extends ASTree> clazz) {
        reset(clazz);
    }

    /*
     * 构造器, 根据已有 Parser 对象组合出新的 Parser 对象.
     * 组合后的 Parser 对象包含原 Parser 对象的语法规则, 在此基础上可以添加新
     * 语法规则.
     */
    protected Parser(Parser p) {
        elements = p.elements;
        factory = p.factory;
    }

    /*
     * 执行语法分析.
     * 这毫无疑问是最重要的方法了.
     * parse 的参数是词法分析器.
     * parse 的返回值是抽象语法树(的根节点).
     *
     * 首先, 我们组合一个 Parser 对象出来, 比如组合后的 Parser 对象叫做 program.
     * program 是一个组合后的对象, 用于解析 program 的语法规则, 嗯, 体现什么解析
     * 组合子之类的扯淡.
     * 怎么组合 Parser 对象见 BasicParser.
     *
     * 一旦组合完毕, Parser.elements 列表中就包含了遍历 program 的语法规则所需要
     * 的所有对象, 每一个对象都用于遍历 program 中的简单形式的语法规则.
     *
     * elements 中的每个用于处理简单语法规则的对象, 在调用它们的 parse 方法后,
     * 它们都会将处理完语法规则后的抽象语法树(的根节点)添加到 results 中,
     * results 是一个存放 ASTree 节点的 List.
     *
     * 所以我们只需要一个 for loop 遍历 elements, 调用 e 的 parse 方法.
     *
     * 嗯, 然后我们返回一个指向 results 的节点, 也就是抽象语法树的根节点. 
     *
     * 当然了, 这必须是递归的.
     */
    public ASTree parse(Lexer lexer) throws ParseException {
        ArrayList<ASTree> results = new ArrayList<ASTree>();
        for (Element e: elements)
            e.parse(lexer, results);

        return factory.make(results);
    }

    protected boolean match(Lexer lexer) throws ParseException {
        if (elements.size() == 0)
            return true;
        else {
            Element e = elements.get(0);
            return e.match(lexer);
        }
    }

    /* create Parser && reset Parser. */
    public static Parser rule() { return rule(null); }

    /* create Parser */
    public static Parser rule(Class<? extends ASTree> clazz) {
        return new Parser(clazz);
    }

    /*
     * 一个全新的 Parser, 清空其语法规则就可以了.
     * 要清空语法规则, 只要清空 elements 就可以了.
     * 要清空 elements, 让 elements 指向一个全新的容器就可以了.
     * ...带垃圾回收的语言还是挺好用的...
     */
    public Parser reset() {
        elements = new ArrayList<Element>();
        return this;
    }

    /* 清空语法规则, 而其(抽象语法树)节点类为 clazz */
    public Parser reset(Class<? extends ASTree> clazz) {
        elements = new ArrayList<Element>();
        factory = Factory.getForASTList(clazz);
        return this;
    }

    /* 向语法规则中加入终结符 (整型字面量) */
    public Parser number() {
        return number(null);
    }

    /* 向语法规则中加入终结符 (整型字面量) */
    public Parser number(Class<? extends ASTLeaf> clazz) {
        elements.add(new NumToken(clazz));
        return this;
    }

    /* 向语法规则中添加终结符 (除保留字 reserved 的标识符) */
    public Parser identifier(HashSet<String> reserved) {
        return identifier(null, reserved);
    }

    /* 向语法规则中添加终结符 (除保留字 reserved 的标识符) */
    public Parser identifier(Class<? extends ASTLeaf> clazz,
                             HashSet<String> reserved)
    {
        elements.add(new IdToken(clazz, reserved));
        return this;
    }

    /* 向语法规则中添加终结符 (字符串字面量) */
    public Parser string() {
        return string(null);
    }

    /* 向语法规则中添加终结符 (字符串字面量) */
    public Parser string(Class<? extends ASTLeaf> clazz) {
        elements.add(new StrToken(clazz));
        return this;
    }

    /* 向语法规则中添加终结符 (与 pat 匹配的标识符) */
    public Parser token(String... pat) {
        elements.add(new Leaf(pat));
        return this;
    }

    /* 向语法规则中添加未包含于抽象语法树的终结符 (与 pat 匹配的标识符) */
    public Parser sep(String... pat) {
        elements.add(new Skip(pat));
        return this;
    }

    /* 向语法规则中添加非终结符 p */
    public Parser ast(Parser p) {
        elements.add(new Tree(p));
        return this;
    }

    /*
     * 向语法规则中添加若干个由 or 关系连接的非终结符 p
     * 前面已经说过, 不能完全表达 BNF 中的 |
     */
    public Parser or(Parser... p) {
        elements.add(new OrTree(p));
        return this;
    }

    /* 
     * 向语法规则中添加可省略的非终结符 p (如果省略, 则作为一颗仅有根节点的
     * 抽象语法树处理)
     */
    public Parser maybe(Parser p) {
        Parser p2 = new Parser(p);
        p2.reset();
        elements.add(new OrTree(new Parser[] { p, p2 }));
        return this;
    }

    /* 向语法规则中添加可省略的非终结符 p */
    public Parser option(Parser p) {
        elements.add(new Repeat(p, true));
        return this;
    }

    /*
     * 向语法规则中添加至少重复出现 0 次的非终结符 p
     * 也即表达 BNF 中的 { }
     */
    public Parser repeat(Parser p) {
        elements.add(new Repeat(p, false));
        return this;
    }

    /* 向语法规则中添加双目运算表达式(subexp 是因子, operators 是运算符列表) */
    public Parser expression(Parser subexp, Operators operators) {
        elements.add(new Expr(null, subexp, operators));
        return this;
    }

    /* 向语法规则中添加双目运算表达式(subexp 是因子, operators 是运算符列表) */
    public Parser expression(Class<? extends ASTree> clazz, Parser subexp,
                             Operators operators) {
        elements.add(new Expr(clazz, subexp, operators));                         
        return this;
    }

    /* 为语法规则起始处的 or 添加新的分支选项 */
    public Parser insertChoice(Parser p) {
        Element e = elements.get(0);
        if (e instanceof OrTree)
            ((OrTree)e).insert(p);
        else {
            Parser otherwise = new Parser(this);
            reset(null);
            or(p, otherwise);
        }
        return this;
    }
}
