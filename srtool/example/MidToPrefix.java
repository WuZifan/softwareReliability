package example;

import java.util.Stack;

public class MidToPrefix {

	/**
	 * 以整型数为例测试中缀表达式转换成前缀表达式的计算问题
	 * 
	 * @author where
	 * 
	 */

	public static void main(String[] args) {
		String input_expression = "(3+4)-5*9";
		System.out.println("待测试的中缀表达式为：" + input_expression);
		System.out.print("相应的前缀表达式为：");
		toPrefixExpression(input_expression);

	}

	/**
	 * 将中缀表达式转化为前缀表达式
	 * 
	 * @param input
	 *            要被转化的中缀表达式
	 */
	public static Stack toPrefixExpression(String input) {
		int len = input.length();// 中缀表达式的长度
		// System.out.println("读到的字符串为："+input+"长度为："+ len);
		char c, tempChar;// 这两个都是中间变量，c用来存放循环中的对应位置的字符，
		Stack<Character> s1 = new Stack<Character>();// 实例化一个符号栈
		Stack<Integer> s2 = new Stack<Integer>();// 实例化一个数字栈
		Stack<Object> expression = new Stack<Object>(); // 实例化一个前缀表达式的栈
		// 从右至左扫描表达式
		for (int i = len - 1; i >= 0; --i) {
			c = input.charAt(i);
			// 判断读取的是不是数字，是的话将数字压入操作数栈和表达式栈
			if (Character.isDigit(c)) {
				String s = String.valueOf(c);
				// 再转换成 Int类型：
				int j = Integer.parseInt(s);
				s2.push(j);
				expression.push(j);
			} else if (isOperator(c)) {
				// 如果当前字符为运算符（包含括号）
				while (!s1.isEmpty() && s1.peek() != ')' && priorityCompare(c, s1.peek()) < 0) {
					// 当前运算符栈不为空且要运算符栈顶运算符不是右括号且当前运算符的优先级比运算符栈顶运算符的优先级低，
					// 则将运算符栈栈顶元素拿出来与操作数栈的两个栈顶元素进行运算并把运算结果压入操作数栈
					expression.push(s1.peek());
					s2.push(calc(s2.pop(), s2.pop(), s1.pop()));
				}
				s1.push(c);
			} else if (c == ')') {
				// 因为我们是从右至左来扫描中缀表达式的所以对于一个“（）”而言一定是先读到右边的括号
				s1.push(c);
			} else if (c == '(') {
				// 如果是左括号“(”，则依次弹出S1栈顶的运算符，并压入表达式栈，直到遇到左括号为止，此时将这一对括号丢弃；
				while ((tempChar = s1.pop()) != ')') {
					expression.push(tempChar);
					s2.push(calc(s2.pop(), s2.pop(), tempChar));
					if (s1.isEmpty()) {
						throw new IllegalArgumentException("bracket dosen't match, missing right bracket ')'.");
					}
				}
			} else if (c == ' ') {
				// 如果表达式里包含空格则不处理空格
			} else {
				throw new IllegalArgumentException("wrong character '" + c + "'");
			}
		}
		while (!s1.isEmpty()) {
			tempChar = s1.pop();
			expression.push(tempChar);
			s2.push(calc(s2.pop(), s2.pop(), tempChar));
		}
//		while (!expression.isEmpty()) {
//			System.out.print(expression.pop() + " ");
//		}
		int result = s2.pop();
		if (!s2.isEmpty())
			throw new IllegalArgumentException("input is a wrong expression.");
		System.out.println();
		System.out.println("计算结果为： " + result);
		return expression;
	}

	/**
	 * 对给定的两个操作数及操作符进行计算
	 * 
	 * @param num1
	 * @param num2
	 * @param op
	 * @return 返回计算整型结果
	 */
	private static Integer calc(int num1, int num2, char op) {

		switch (op) {
		case '+':
			return num1 + num2;
		case '-':
			return num1 - num2;
		case '*':
			return num1 * num2;
		case '/':
			if (num2 == 0)
				throw new IllegalArgumentException("divisor can't be 0.");
			return num1 / num2;
		default:
			return 0; // will never catch up here
		}

	}

	/**
	 * 判断字符是否是操作符的方法
	 * 
	 * @param c
	 * @return
	 */
	private static boolean isOperator(char c) {
		return (c == '+' || c == '-' || c == '*' || c == '/');
	}

	/**
	 * 判断运算符优先级的方法
	 * 
	 * @param op1
	 * @param op2
	 * @return 返回值如果是: - 1则表示op1的优先级低于op2, 0 则表示op1的优先级等于op2， 1则表示op1的优先级高于op2。
	 */
	private static int priorityCompare(char op1, char op2) {
		switch (op1) {
		case '+':
		case '-':
			return (op2 == '*' || op2 == '/' ? -1 : 0);
		case '*':
		case '/':
			return (op2 == '+' || op2 == '-' ? 1 : 0);
		}
		return 1;
	}
}
