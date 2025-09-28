---
title: K8s on Hetzner vs. AWS Fargate
date: 2025-28-09
tags: ["theoretical physics", "quantum gravity"]
subtitle: Total Cost of Ownership analysis for IT-departments
---

# Introduction

This comparison evaluates self-managed Kubernetes clusters deployed on Hetzner Cloud or dedicated servers against AWS ECS Fargate as a fully managed container platform. The analysis considers the total cost of ownership (TCO) over a three-year period, factoring in infrastructure pricing, staffing needs, operational complexity, and scalability.

For simplicity, the cost calculations include only compute usage and exclude storage, bandwidth, and other components. We assume that fewer employees are needed to operate and maintain a highly managed service compared to a traditional setup, with the least operational effort required for SaaS offerings. The following illustration highlights the different levels of management.

![](/images/managed-levels.png)

The more self-management is required (blue), the more working hours you need to invest in the system and the more staff you will likely require.

A Kubernetes cluster on Hetzner is considered to fall somewhere between traditional IT and IaaS. Hetzner provides the physical servers, storage, and networking, but everything beyond that is managed by the customer. AWS ECS Fargate, on the other hand, is a PaaS solution; you only need to manage your application and its data. Please note that unless your Docker image is built entirely from scratch, you will typically need to maintain or at least support developers in updating their Dockerfile.

## Cost structure and TCO Analysis

| Category                 | Hetzner Kubernetes                                                | AWS ECS Fargate                                                      |
| ------------------------ | ----------------------------------------------------------------- | -------------------------------------------------------------------- |
| **VM/Compute (monthly)** | 2 vCPU + 4 GB: ~$6<br>4 vCPU + 8 GB: ~$17<br>8 vCPU + 16 GB: ~$33 | 2 vCPU + 4 GB: ~$55<br>4 vCPU + 8 GB: ~$110<br>8 vCPU + 16 GB: ~$210 |
| **Staffing (annual)**    | 5–10 DevOps engineers, ~$500k–1,000k per year                     | 1–3 Cloud engineers, ~$100k–300k per year                            |
| **3-Year Staffing TCO**  | ~$1.5M–3.0M                                                       | ~$300k–900k                                                          |

In addition to cloud VMs, Hetzner also offers dedicated servers. These provide substantially more compute at a lower per-vCPU cost but demand a much higher level of self-management and therefore more staff, as they lack even basic functionality such as snapshotting, backups, automatic provisioning through a CLI, or Kubernetes plugins.

We assume a baseline of **100k for one DevOps/Cloud Engineer per year**. This number can vary greatly across different countries. It's possible to adjust the given numbers and do a recalculation with the interactive TCO calculator.

![](/images/tco.png)

As you can see, up to approximately 666 vCPUs, AWS Fargate is the more cost-effective option. In the range between 666 and 3,000 vCPUs, a more detailed cost analysis is necessary. For anything beyond that, Hetzner becomes the better choice.

## TCO calculator 

In order to do your own calculation, please use the TCO calculator below.

{% raw %}
<style>
.tco-calculator {
  --bg-light: #f8f9fa;
  --bg-dark: #2d3748;
  --border-light: #dee2e6;
  --border-dark: #4a5568;
  --text-light: #495057;
  --text-dark: #e2e8f0;
  --info-bg-light: #e3f2fd;
  --info-bg-dark: #2a4365;
  --canvas-bg-light: #ffffff;
  --canvas-bg-dark: #1a202c;
  
  background: var(--bg-light);
  border: 1px solid var(--border-light);
  border-radius: 8px;
  padding: 20px;
  margin: 20px 0;
  transition: background-color 0.3s ease, border-color 0.3s ease;
}

.tco-calculator.dark-mode {
  background: var(--bg-dark);
  border-color: var(--border-dark);
}

.tco-calculator h4 {
  color: var(--text-light);
  margin-top: 0;
  transition: color 0.3s ease;
}

.tco-calculator.dark-mode h4 {
  color: var(--text-dark);
}

.tco-calculator label {
  font-weight: bold;
  display: block;
  margin-bottom: 5px;
  color: var(--text-light);
  transition: color 0.3s ease;
}

.tco-calculator.dark-mode label {
  color: var(--text-dark);
}

.tco-calculator input[type="range"] {
  width: 100%;
  margin-bottom: 10px;
  accent-color: #4ecdc4;
  height: 6px;
  -webkit-appearance: none;
  appearance: none;
  border-radius: 3px;
  background: #ddd;
  outline: none;
}

.tco-calculator input[type="range"]::-webkit-slider-thumb {
  -webkit-appearance: none;
  appearance: none;
  height: 20px;
  width: 20px;
  border-radius: 50%;
  background: #4ecdc4;
  cursor: pointer;
}

.tco-calculator input[type="range"]::-moz-range-thumb {
  height: 20px;
  width: 20px;
  border-radius: 50%;
  background: #4ecdc4;
  cursor: pointer;
  border: none;
}

.tco-calculator #tcoChart {
  max-width: 100%;
  background: var(--canvas-bg-light);
  border-radius: 4px;
  transition: background-color 0.3s ease;
}

.tco-calculator.dark-mode #tcoChart {
  background: var(--canvas-bg-dark);
}

.tco-calculator #intersectionPoint {
  text-align: center;
  padding: 12px;
  background: var(--info-bg-light);
  border-radius: 4px;
  font-weight: bold;
  color: var(--text-light);
  transition: background-color 0.3s ease, color 0.3s ease;
  min-height: 20px;
  margin-top: 10px;
  font-size: 16px;
}

.tco-calculator.dark-mode #intersectionPoint {
  background: var(--info-bg-dark);
  color: var(--text-dark);
}

.tco-grid {
  display: grid;
  grid-template-columns: 1fr 1fr 1fr;
  gap: 25px;
  margin-bottom: 20px;
  align-items: end;
}

.tco-grid > div {
  display: flex;
  flex-direction: column;
}

.tco-grid label {
  margin-bottom: 8px;
  min-height: 20px;
  display: flex;
  align-items: center;
}

@media (max-width: 768px) {
  .tco-grid {
    grid-template-columns: 1fr;
    gap: 20px;
  }
}
</style>

<div class="tco-calculator" id="tcoCalculator">
  <h4>Interactive TCO Calculator</h4>
  
  <div class="tco-grid">
    <div>
      <label for="hetznerStaff">Hetzner DevOps Engineers: <span id="hetznerStaffValue">7</span></label>
      <input type="range" id="hetznerStaff" min="1" max="15" value="7">
    </div>
    
    <div>
      <label for="awsStaff">AWS Cloud Engineers: <span id="awsStaffValue">2</span></label>
      <input type="range" id="awsStaff" min="1" max="10" value="2">
    </div>
    
    <div>
      <label for="engineerSalary">Engineer Salary (USD): <span id="salaryValue">$100,000</span></label>
      <input type="range" id="engineerSalary" min="10000" max="500000" value="100000" step="5000">
    </div>
  </div>

  <div style="margin-bottom: 20px;">
    <canvas id="tcoChart" width="800" height="400"></canvas>
  </div>
  
  <div id="intersectionPoint"></div>
</div>

<script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
<script>
let tcoChart;
let isDarkMode = false;

// Dark mode detection and handling
function checkDarkMode() {
  // Check if dark-mode-toggle is present and has dark mode enabled
  const darkModeToggle = document.querySelector('dark-mode-toggle');
  if (darkModeToggle) {
    isDarkMode = darkModeToggle.mode === 'dark';
  } else {
    // Fallback to prefers-color-scheme
    isDarkMode = window.matchMedia('(prefers-color-scheme: dark)').matches;
  }
  
  // Apply dark mode class to calculator
  const calculator = document.getElementById('tcoCalculator');
  if (isDarkMode) {
    calculator.classList.add('dark-mode');
  } else {
    calculator.classList.remove('dark-mode');
  }
  
  return isDarkMode;
}

function getChartColors() {
  const dark = checkDarkMode();
  
  return {
    gridColor: dark ? '#4a5568' : '#e2e8f0',
    textColor: dark ? '#e2e8f0' : '#495057',
    backgroundColor: dark ? '#1a202c' : '#ffffff',
    hetznerColor: dark ? '#ff8a8a' : '#ff6b6b',
    awsColor: dark ? '#66d9d1' : '#4ecdc4'
  };
}

function initChart() {
  const ctx = document.getElementById('tcoChart').getContext('2d');
  const colors = getChartColors();
  
  tcoChart = new Chart(ctx, {
    type: 'line',
    data: {
      labels: [],
      datasets: [
        {
          label: 'Hetzner Kubernetes',
          data: [],
          borderColor: colors.hetznerColor,
          backgroundColor: `${colors.hetznerColor}20`,
          borderWidth: 3,
          fill: false,
          tension: 0.4,
          pointRadius: 0,
          pointHoverRadius: 6,
          pointHoverBackgroundColor: colors.hetznerColor,
          pointHoverBorderColor: colors.hetznerColor,
          pointHoverBorderWidth: 2
        },
        {
          label: 'AWS ECS Fargate',
          data: [],
          borderColor: colors.awsColor,
          backgroundColor: `${colors.awsColor}20`,
          borderWidth: 3,
          fill: false,
          tension: 0.4,
          pointRadius: 0,
          pointHoverRadius: 6,
          pointHoverBackgroundColor: colors.awsColor,
          pointHoverBorderColor: colors.awsColor,
          pointHoverBorderWidth: 2
        }
      ]
    },
    options: {
      responsive: true,
      interaction: {
        mode: 'index',
        intersect: false,
      },
      plugins: {
        title: {
          display: true,
          text: '3-Year TCO vs Average vCPUs: Hetzner Kubernetes vs AWS ECS Fargate',
          color: colors.textColor,
          font: {
            size: 14,
            weight: 'bold'
          }
        },
        legend: {
          display: true,
          labels: {
            color: colors.textColor,
            usePointStyle: true,
            padding: 20
          }
        }
      },
      scales: {
        x: {
          title: {
            display: true,
            text: 'Average vCPUs used (monthly)',
            color: colors.textColor
          },
          ticks: {
            color: colors.textColor
          },
          grid: {
            color: colors.gridColor
          }
        },
        y: {
          title: {
            display: true,
            text: 'TCO over 3 years (Million USD)',
            color: colors.textColor
          },
          ticks: {
            color: colors.textColor
          },
          grid: {
            color: colors.gridColor
          }
        }
      }
    }
  });
}

function updateChartTheme() {
  if (!tcoChart) return;
  
  const colors = getChartColors();
  
  // Update dataset colors
  tcoChart.data.datasets[0].borderColor = colors.hetznerColor;
  tcoChart.data.datasets[0].backgroundColor = `${colors.hetznerColor}20`;
  tcoChart.data.datasets[0].pointHoverBackgroundColor = colors.hetznerColor;
  tcoChart.data.datasets[0].pointHoverBorderColor = colors.hetznerColor;
  tcoChart.data.datasets[1].borderColor = colors.awsColor;
  tcoChart.data.datasets[1].backgroundColor = `${colors.awsColor}20`;
  tcoChart.data.datasets[1].pointHoverBackgroundColor = colors.awsColor;
  tcoChart.data.datasets[1].pointHoverBorderColor = colors.awsColor;
  
  // Update chart options colors
  tcoChart.options.plugins.title.color = colors.textColor;
  tcoChart.options.plugins.legend.labels.color = colors.textColor;
  tcoChart.options.scales.x.title.color = colors.textColor;
  tcoChart.options.scales.x.ticks.color = colors.textColor;
  tcoChart.options.scales.x.grid.color = colors.gridColor;
  tcoChart.options.scales.y.title.color = colors.textColor;
  tcoChart.options.scales.y.ticks.color = colors.textColor;
  tcoChart.options.scales.y.grid.color = colors.gridColor;
  
  tcoChart.update('none'); // Update without animation
}

function calculateTCO() {
  const hetznerStaff = parseInt(document.getElementById('hetznerStaff').value);
  const awsStaff = parseInt(document.getElementById('awsStaff').value);
  const engineerSalary = parseInt(document.getElementById('engineerSalary').value);
  const maxVCPU = 5000; // Fixed at 5,000 vCPUs
  
  // Constants
  const years = 3;
  const hetznerPerVCPUMonth = 2;
  const awsPerVCPUMonth = 27;
  
  // Generate vCPU range
  const vcpuPoints = [];
  const step = Math.max(1, Math.floor(maxVCPU / 100));
  for (let i = 0; i <= maxVCPU; i += step) {
    vcpuPoints.push(i);
  }
  
  // Calculate TCO curves
  const hetznerData = vcpuPoints.map(v => 
    (years * hetznerStaff * engineerSalary + 36 * hetznerPerVCPUMonth * v) / 1e6
  );
  const awsData = vcpuPoints.map(v => 
    (years * awsStaff * engineerSalary + 36 * awsPerVCPUMonth * v) / 1e6
  );
  
  // Calculate intersection point (break-even)
  const staffCostDiff = years * (hetznerStaff - awsStaff) * engineerSalary;
  const vcpuCostDiff = 36 * (awsPerVCPUMonth - hetznerPerVCPUMonth);
  const intersectionVCPU = staffCostDiff / vcpuCostDiff;
  
  // Update chart
  tcoChart.data.labels = vcpuPoints;
  tcoChart.data.datasets[0].data = hetznerData;
  tcoChart.data.datasets[1].data = awsData;
  tcoChart.update();
  
  // Display intersection point
  const intersectionDisplay = document.getElementById('intersectionPoint');
  console.log(`Hetzner: ${hetznerStaff}, AWS: ${awsStaff}, Salary: ${engineerSalary}`);
  console.log(`Intersection calculation: staffCostDiff=${staffCostDiff}, vcpuCostDiff=${vcpuCostDiff}, intersectionVCPU=${intersectionVCPU}`);
  console.log('Element found:', intersectionDisplay ? 'Yes' : 'No');
  
  if (intersectionDisplay) {
    if (intersectionVCPU > 0) {
      intersectionDisplay.textContent = `Break-even point: ${intersectionVCPU.toFixed(1)} vCPUs`;
      intersectionDisplay.style.display = 'block';
    } else {
      intersectionDisplay.textContent = '';
      intersectionDisplay.style.display = 'none';
    }
  }
}

function enforceStaffConstraints(changedSlider) {
  const hetznerSlider = document.getElementById('hetznerStaff');
  const awsSlider = document.getElementById('awsStaff');
  const hetznerValue = parseInt(hetznerSlider.value);
  const awsValue = parseInt(awsSlider.value);
  
  if (changedSlider === 'hetzner') {
    // If Hetzner < AWS, reduce AWS to match Hetzner
    if (hetznerValue < awsValue) {
      awsSlider.value = hetznerValue;
    }
  } else if (changedSlider === 'aws') {
    // If AWS > Hetzner, increase Hetzner to match AWS (maximum 15)
    if (awsValue > hetznerValue) {
      hetznerSlider.value = Math.min(15, awsValue);
    }
  }
}

function updateLabels() {
  const hetznerStaff = document.getElementById('hetznerStaff').value;
  const awsStaff = document.getElementById('awsStaff').value;
  const salary = parseInt(document.getElementById('engineerSalary').value);
  
  document.getElementById('hetznerStaffValue').textContent = hetznerStaff;
  document.getElementById('awsStaffValue').textContent = awsStaff;
  document.getElementById('salaryValue').textContent = `$${salary.toLocaleString()}`;
}

// Initialize when page loads
document.addEventListener('DOMContentLoaded', function() {
  // Check initial dark mode state
  checkDarkMode();
  
  // Initialize chart
  initChart();
  updateLabels();
  calculateTCO();
  
  // Add event listeners to sliders with constraints
  document.getElementById('hetznerStaff').addEventListener('input', function() {
    enforceStaffConstraints('hetzner');
    updateLabels();
    calculateTCO();
  });
  
  document.getElementById('awsStaff').addEventListener('input', function() {
    enforceStaffConstraints('aws');
    updateLabels();
    calculateTCO();
  });
  
  document.getElementById('engineerSalary').addEventListener('input', function() {
    updateLabels();
    calculateTCO();
  });
  
  // Listen for dark mode toggle changes
  document.addEventListener('colorschemechange', function(e) {
    console.log(`Color scheme changed to ${e.detail.colorScheme}`);
    updateChartTheme();
  });
  
  // Fallback: listen for system dark mode changes if no toggle is present
  if (!document.querySelector('dark-mode-toggle')) {
    window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', function() {
      updateChartTheme();
    });
  }
});
</script>
{% endraw %}

The interactive calculator above shows the 3-year TCO compared to the average monthly vCPUs. You can adjust the staffing levels and salary to match your specific situation and immediately see how the break-even point changes.

## Conclusion
For small to mid-sized IT-Departments, AWS Fargate usually minimizes TCO once staffing is factored in. Hetzner Kubernetes may be attractive if infrastructure cost savings are substantial and the company already has a strong DevOps team. However, the operational risk and manpower overhead are significant.

AWS Fargate is generally more suitable when predictability, scalability, and reduced staffing costs are priorities. Hetzner Kubernetes is only preferable when raw infrastructure savings outweigh the additional DevOps staffing and operational risks over a multi-year horizon.
