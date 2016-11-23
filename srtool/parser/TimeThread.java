package parser;

public class TimeThread extends Thread {

	public boolean quitThread = false;

	@Override
	public void run() {
		double i = 0;
		while (!this.quitThread) {
			try {
				// sleep for 1 second
				Thread.sleep(50);
				i = i + 0.05;
				if (i >0.15) {
					this.quitThread=true;
					break;
				}
				
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
			System.out.println("Processing....Already spent" + i + "second(s)");
		}
		throw new RuntimeException();
	}

}
