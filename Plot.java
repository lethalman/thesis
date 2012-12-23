import java.awt.image.*;
import java.io.*;
import java.awt.*;
import org.jfree.data.*;
import org.jfree.data.xy.*;
import org.jfree.chart.*;
import org.jfree.chart.axis.*;
import org.jfree.chart.renderer.xy.*;
import org.jfree.chart.plot.*;
import org.jfree.data.general.*;
import org.jfree.data.general.*;
import org.jfree.util.*;
import javax.imageio.*;

public class Plot {
    class Data {
	double x;
	double y1;
	double y2;

	public Data (double x, double y1, double y2) {
	    this.x = x;
	    this.y1 = y1;
	    this.y2 = y2;
	}
    }

    void fillChart (JFreeChart chart, BufferedReader r) throws IOException {
	XYPlot p = (XYPlot) chart.getPlot();
	String line = r.readLine ();
	String[] fields = line.split(",");
	chart.setTitle (fields[0]);
	p.getDomainAxis().setLabel (fields[1]);

	NumberAxis a1 = new NumberAxis (fields[2]);
	p.setRangeAxis (0, a1);
	XYSeries series1 = new XYSeries (fields[3]);
	XYSeries series2 = new XYSeries (fields[4]);
	XYSeriesCollection dataset1 = new XYSeriesCollection ();
	dataset1.addSeries (series1);
	dataset1.addSeries (series2);
	p.setDataset (0, dataset1);
	p.mapDatasetToRangeAxis (0, 0);
	XYLineAndShapeRenderer renderer1 = new XYLineAndShapeRenderer();
	p.setRenderer(0, renderer1);

	XYSeries series3 = new XYSeries ("");
	XYSeries series4 = new XYSeries ("");
	boolean hasSecondary = fields.length > 5;
	if (hasSecondary) {
	    NumberAxis a2 = new NumberAxis (fields[5]);
	    p.setRangeAxis (1, a2);
	    series3.setKey (fields[6]);
	    series4.setKey (fields[7]);
	    XYSeriesCollection dataset2 = new XYSeriesCollection ();
	    dataset2.addSeries (series3);
	    dataset2.addSeries (series4);
	    p.setDataset (1, dataset2);
	    p.mapDatasetToRangeAxis (1, 1);
	    XYLineAndShapeRenderer r2 = new XYLineAndShapeRenderer();
	    p.setRenderer (1, r2);
	}

	double max = 0;
	double min = 1;

        while (true) {
            line = r.readLine ();
            if (line == null) {
                break;
            }
            fields = line.split (",");
	    int x = Integer.parseInt (fields[0]);
	    double y1 = Double.parseDouble (fields[1]);
	    double y2 = Double.parseDouble (fields[2]);
	    series1.add (x, y1);
	    series2.add (x, y2);
	    if (hasSecondary) {
		double y3 = Double.parseDouble (fields[3]);
		double y4 = Double.parseDouble (fields[4]);
		series3.add (x, y3);
		series4.add (x, y4);
		max = Math.max (max, Math.max (y3, y4));
		min = Math.min (min, Math.min (y3, y4));
	    }
        }
        r.close ();
    }

    public void plot (String filename) throws IOException {
	BufferedReader r = new BufferedReader (new FileReader (filename));
	JFreeChart chart = createChart (r);
	output (chart);
    }
    
    JFreeChart createChart (BufferedReader r) throws IOException {
	JFreeChart chart = ChartFactory.createXYLineChart ("",  
							   "",
							   "",
							   null,
							   PlotOrientation.VERTICAL,
							   true,
							   true,
							   false);
	fillCompareChart (chart, r);
	fillDescribeChart (chart, r);
        return chart;
    }

    void output (JFreeChart chart) throws IOException {
	ChartPanel chartPanel = new ChartPanel(chart);
	Dimension size = chartPanel.getPreferredSize();
	ChartUtilities.saveChartAsPNG (new File ("plot.png"), chart, (int)size.getWidth(), (int)size.getHeight());
    }

    public static void main (String[] args) throws IOException {
	new Plot().plot ("preferred_args_same_error.csv");
    }
}