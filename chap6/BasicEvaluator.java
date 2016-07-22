package chap6;

import javassist.gluonj.*;
import stone.Token;
import stone.StoneException;
import stone.ast.*;
import java.util.List;

/*
 * eval 的实现逻辑很简单: 使用 DFS(Depth First Search) 遍历 AST, 调用子树的
 * eval 方法.
 * eval 的参数是 Evironment 对象, 返回值是 Object 对象.
 * 
 * 由于要调用子树的 eval 方法, 这意味着每个 ASTree Node 都应该有 eval 方法.
 * 而 AST 已经设计完毕, 设计 AST 时并未考虑 eval.
 * 所以这里使用了名为 GluonJ 的系统/库, @Reviser 标记表示"修改器", 其作用是
 * 修改/重写原来设计好的类. 比如 ASTreeEx 将修改/重写 ASTree, 向 ASTree 中加入
 * eval 方法.
 * 当然不使用 GluonJ 系统也是可以的, 就是改 AST 了, 改起来也不是很困难^_^
 * GluonJ 系统使得就算需要扩展类的定义, 也不需要修改原有的类, 简直让"开放-封闭"
 * 原则可以被直接无视, 所以 GluonJ 还是非常强大的.
 *
 * 还需要注意的就是, eval 计算的是 R-value. 含有 = 运算符的赋值表达式, 其
 * L-value 需要 computeAssign 处理. 参见 BinaryExpr 类的 eval 方法.
 * 从语法规则上看, = 左侧也算 expression. 然而语义上, = 左侧并非 expression.
 */
@Reviser
public class BasicEvaluator {
    public static final int TRUE = 1;
    public static final int FALSE = 0;

    @Reviser
    public static abstract class ASTreeEx extends ASTree {
        public abstract Object eval(Environment env);
    }

    @Reviser
    public static class ASTListEx extends ASTList {
        public ASTListEx(List<ASTree> c) { super(c); }
        public Object eval(Environment env) {
            throw new StoneException("cannot eval: " + toString(), this);
        }
    }

    @Reviser
    public static class ASTLeafEx extends ASTLeaf {
        public ASTLeafEx(Token t) { super(t); }
        public Object eval(Environment env) {
            throw new StoneException("cannot eval: " + toString(), this);
        }
    }

    @Reviser
    public static class NumberEx extends NumberLiteral {
        public NumberEx(Token t) { super(t); }
        public Object eval(Environment env) { return value(); }
    }

    @Reviser
    public static class StringEx extends StringLiteral {
        public StringEx(Token t) { super(t); }
        public Object eval(Environment env) { return value(); }
    }

    @Reviser
    public static class NameEx extends Name {
        public NameEx(Token t) { super(t); }
        public Object eval(Environment env) { 
            Object value = env.get(name());
            if (value == null)
                throw new StoneException("undefined name: " + name(), this);
            else
                return value;
        }
    }

    @Reviser
    public static class NegativeEx extends NegativeExpr {
        public NegativeEx(List<ASTree> c) { super(c); }
        public Object eval(Environment env) {
            Object v = ((ASTreeEx)operand()).eval(env);
            if (v instanceof Integer)
                return new Integer(-((Integer)v).intValue());
            else
                throw new StoneException("bad type for -", this);
        }
    }

    @Reviser
    public static class BinaryEx extends BinaryExpr {
        public BinaryEx(List<ASTree> c) { super(c); }
        public Object eval(Environment env) {
            String op = operator();
            if ("=".equals(op)) {
                Object right = ((ASTreeEx)right()).eval(env);
                return computeAssign(env, right);
            }
            else {
                Object left = ((ASTreeEx)left()).eval(env);
                Object right = ((ASTreeEx)right()).eval(env);
                return computeOp(left, op, right);
            }
        }

        protected Object computeAssign(Environment env, Object rvalue) {
            ASTree l = left();
            if (l instanceof Name) {
                env.put(((Name)l).name(), rvalue);
                return rvalue;
            }
            else
                throw new StoneException("bad assignment", this);
        }
 
        protected Object computeOp(Object left, String op, Object right) {
            if (left instanceof Integer && right instanceof Integer) {
                return computeNumber((Integer)left, op, (Integer)right);
            }
            else {
                if (op.equals("+"))
                    return String.valueOf(left) + String.valueOf(right);
                else if (op.equals("==")) {
                    if (left == null)
                        return right == null ? TRUE : FALSE;
                    else
                        return left.equals(right) ? TRUE : FALSE;
                }
                else
                    throw new StoneException("bad type", this);
            }
        }

        protected Object computeNumber(Integer left, String op, Integer right) {
            int a = left.intValue();
            int b = right.intValue();
            if (op.equals("+"))
                return a + b;
            else if (op.equals("-"))
                return a - b;
            else if (op.equals("*"))
                return a * b;
            else if (op.equals("/"))
                return a / b;
            else if (op.equals("%"))
                return a % b;
            else if (op.equals("=="))
                return a == b ? TRUE : FALSE;
            else if (op.equals(">"))
                return a > b ? TRUE : FALSE;
            else if (op.equals("<"))
                return a < b ? TRUE : FALSE;
            else
                throw new StoneException("bad operator", this);
        }
    }

    @Reviser
    public static class BlockEx extends BlockStmnt {
        public BlockEx(List<ASTree> c) { super(c); }
        public Object eval(Environment env) {
            Object result = 0;
            for (ASTree t: this) {
                if (!(t instanceof NullStmnt))
                    result = ((ASTreeEx)t).eval(env);
            }
            return result;
        }
    }

    @Reviser
    public static class IfEx extends IfStmnt {
        public IfEx(List<ASTree> c) { super(c); }
        public Object eval(Environment env) {
            Object c = ((ASTreeEx)condition()).eval(env);
            if (c instanceof Integer && ((Integer)c).intValue() != FALSE)
                return ((ASTreeEx)thenBlock()).eval(env);
            else {
                ASTree b = elseBlock();
                if (b == null)
                    return 0;
                else
                    return ((ASTreeEx)b).eval(env);
            }
        }
    }

    @Reviser
    public static class WhileEx extends WhileStmnt {
        public WhileEx(List<ASTree> c) { super(c); }
        public Object eval(Environment env) {
            Object result = 0;
            for (;;) {
                Object c = ((ASTreeEx)condition()).eval(env);
                if (c instanceof Integer && ((Integer)c).intValue() == FALSE)
                    return result;
                else
                    result = ((ASTreeEx)body()).eval(env);
            }
        }
    }
}
