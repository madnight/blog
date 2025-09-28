---
title: K8s on Hetzner vs. AWS Fargate
date: 2025-28-09
tags: ["AWS", "hetzner", "kubernetes", "fargate", "cloud engineering"]
subtitle: Total Cost of Ownership analysis for IT-departments
---

# Introduction

This comparison evaluates self-managed Kubernetes clusters deployed on Hetzner Cloud or dedicated servers against AWS ECS Fargate as a fully managed container platform. The analysis considers the total cost of ownership (TCO) over a three-year period, factoring in infrastructure pricing, staffing needs, operational complexity, and scalability.

For simplicity, the cost calculations include only compute usage and exclude storage, bandwidth, and other components. We assume that fewer employees are needed to operate and maintain a highly managed service compared to a traditional setup, with the least operational effort required for SaaS offerings. The following illustration highlights the different levels of management.

![](/images/managed-levels.png)

The more self-management is required (blue), the more working hours you need to invest in the system and the more staff you will likely require.

A Kubernetes cluster on Hetzner is considered to fall somewhere between traditional IT and IaaS. Hetzner provides the physical servers, storage, and networking, but everything beyond that is managed by the customer. AWS ECS Fargate, on the other hand, is a PaaS solution; you only need to manage your application and its data. Please note that unless your Docker image is built entirely from scratch, you will typically need to maintain or at least support developers in updating their Dockerfile.

## Cost structure and Scenarios

| Category                 | Hetzner Kubernetes                                                | AWS ECS Fargate                                                      |
| ------------------------ | ----------------------------------------------------------------- | -------------------------------------------------------------------- |
| **VM/Compute (monthly)** | 2 vCPU + 4 GB: ~$6<br>4 vCPU + 8 GB: ~$17<br>8 vCPU + 16 GB: ~$33 | 2 vCPU + 4 GB: ~$55<br>4 vCPU + 8 GB: ~$110<br>8 vCPU + 16 GB: ~$210 |
| **Staffing (annual)**    | 5-10 DevOps engineers, ~$500k-1,000k per year                     | 1-3 Cloud engineers, ~$100k-300k per year                            |
| **3-Year Staffing TCO**  | ~$1.5M-3.0M                                                       | ~$300k-900k                                                          |

In addition to cloud VMs, Hetzner also offers dedicated servers. These provide substantially more compute at a lower per-vCPU cost but demand a much higher level of self-management and therefore more staff, as they lack even basic functionality such as snapshotting, backups, automatic provisioning through a CLI, or Kubernetes plugins.

We assume a baseline of **$100k for one DevOps/Cloud Engineer per year**. This number can vary greatly across different countries. It's possible to adjust the given numbers and do a recalculation with the interactive TCO calculator.

![](/images/tco.png)

The choice between Hetzner Kubernetes and AWS ECS Fargate depends heavily on your team size, operational expertise, and scale. Here are three representative scenarios:

### **Scenario 1: AWS ECS Fargate Wins** 
*Small to Medium Applications (< 700 vCPUs)*

**Example Setup:** 2 Hetzner DevOps engineers vs. 1 AWS Cloud engineer at $100k salary
**Break-even point:** ~700 vCPUs
**AWS advantage:** Below 700 vCPUs, significantly lower total cost

**Real-world applications:**
- **Early-stage SaaS companies** with 10-50k users running web applications, APIs, and databases
- **Digital agencies** managing multiple client websites and applications
- **E-commerce startups** with moderate traffic (< 1M monthly visitors)
- **Development and staging environments** for larger companies
- **Microservice architectures** with 10-20 small services

**Why AWS wins:** The operational simplicity means you can run lean teams focused on product development rather than infrastructure management. The higher per-vCPU cost is offset by dramatically reduced staffing needs.

### **Scenario 2: It's a Close Call**
*Medium to Large Applications (700-2,500 vCPUs)*

**Example Setup:** 5 Hetzner DevOps engineers vs. 3 AWS Cloud engineers at $100k salary
**Break-even point:** ~1,333 vCPUs
**Decision factors:** Team expertise, growth trajectory, compliance requirements

**Real-world applications:**
- **Growing SaaS platforms** with 100k-1M users experiencing rapid scaling
- **Financial services companies** with moderate compute needs but strict compliance requirements
- **Media companies** running content management systems with variable traffic
- **Healthcare platforms** balancing cost with regulatory compliance
- **Mid-size enterprises** modernizing legacy applications

**Key considerations:** In this range, factors beyond pure cost become crucial - team expertise, security requirements, compliance needs, and growth predictability often determine the winner.

### **Scenario 3: Hetzner Kubernetes Wins**
*Large-scale Applications (> 2,500 vCPUs)*

**Example Setup:** 8 Hetzner DevOps engineers vs. 4 AWS Cloud engineers at $100k salary
**Break-even point:** ~2,000 vCPUs
**Hetzner advantage:** Above 2,000 vCPUs, substantial cost savings despite larger teams

**Real-world applications:**
- **Large e-commerce platforms** (Amazon, Shopify scale) with millions of daily transactions
- **Data processing companies** running analytics, ETL pipelines, and machine learning workloads
- **Gaming companies** with massive multiplayer online games requiring high compute
- **Enterprise software vendors** serving thousands of corporate clients
- **Research institutions** running computational simulations and scientific computing
- **Media streaming services** handling video transcoding and content delivery

**Why Hetzner wins:** At scale, the infrastructure cost difference becomes so significant that even larger DevOps teams are justified. Companies at this level typically already have strong internal platform capabilities.

## Total Cost of Ownership Calculator 

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
  margin: 0;
  padding: 10px 0;
  accent-color: #4ecdc4;
  height: 6px;
  -webkit-appearance: none;
  appearance: none;
  border-radius: 3px;
  background: #ddd;
  outline: none;
}

.tco-calculator.dark-mode input[type="range"] {
  background: #4a5568;
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

.tco-calculator.dark-mode input[type="range"]::-webkit-slider-thumb {
  background: #66d9d1;
}

.tco-calculator input[type="range"]::-moz-range-thumb {
  height: 20px;
  width: 20px;
  border-radius: 50%;
  background: #4ecdc4;
  cursor: pointer;
  border: none;
}

.tco-calculator.dark-mode input[type="range"]::-moz-range-thumb {
  background: #66d9d1;
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
  align-items: start;
}

.tco-grid > div {
  display: flex;
  flex-direction: column;
  min-height: 80px;
}

.tco-grid label {
  margin-bottom: 8px;
  min-height: 24px;
  display: flex;
  align-items: center;
  justify-content: space-between;
  line-height: 1.2;
}

.tco-grid label span {
  font-weight: normal;
  color: var(--text-light);
  margin-left: 8px;
  min-width: 50px;
  text-align: right;
  font-family: 'Courier New', monospace;
  font-variant-numeric: tabular-nums;
}

.tco-calculator.dark-mode .tco-grid label span {
  color: var(--text-dark);
}

@media (max-width: 768px) {
  .tco-grid {
    grid-template-columns: 1fr;
    gap: 20px;
  }
}
</style>

<div class="tco-calculator" id="tcoCalculator">  
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
      <label for="engineerSalary">Engineer Salary (USD): <span id="salaryValue">$100k</span></label>
      <input type="range" id="engineerSalary" min="10000" max="500000" value="100000" step="5000">
    </div>
  </div>

  <div style="margin-bottom: 20px;">
    <canvas id="tcoChart" width="800" height="400"></canvas>
  </div>
  
  <div id="intersectionPoint"></div>
</div>

<script src="https://cdn.jsdelivr.net/npm/chart.js@4.5.0/dist/chart.umd.min.js"></script>
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
  
  if (intersectionDisplay) {
    if (intersectionVCPU > 0) {
      intersectionDisplay.textContent = `Break-even point: ${Math.round(intersectionVCPU)} vCPUs`;
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

function formatSalary(salary) {
  if (salary >= 1000) {
    return `$${Math.round(salary / 1000)}k`;
  } else {
    return `$${salary}`;
  }
}

function updateLabels() {
  const hetznerStaff = document.getElementById('hetznerStaff').value;
  const awsStaff = document.getElementById('awsStaff').value;
  const salary = parseInt(document.getElementById('engineerSalary').value);
  
  document.getElementById('hetznerStaffValue').textContent = hetznerStaff;
  document.getElementById('awsStaffValue').textContent = awsStaff;
  document.getElementById('salaryValue').textContent = formatSalary(salary);
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

## Operational Complexity

To understand why the staffing ratios differ so dramatically, consider what each approach entails. **AWS ECS Fargate** requires defining task definitions, configuring basic networking (**VPC**, **subnets**, **security groups**), and connecting services to load balancers - typically manageable by 1-3 cloud engineers using tools like **Terraform**. The complexity is largely abstracted away by AWS.

Hetzner Kubernetes, in contrast, demands building a production-grade platform from the ground up. Teams must orchestrate server provisioning, install and configure Kubernetes itself (**kubeadm**, **Cluster API**), then deploy approximately 20+ critical supporting systems: networking solutions (**Calico**, **Cilium**), DNS resolution (**CoreDNS**), monitoring stack (**Prometheus**, **Grafana**), ingress controllers (**NGINX**, **Traefik**), certificate management (**cert-manager**), backup systems (**Velero**), GitOps tools (**Argo CD**, **Flux**), storage integration (**CSI drivers**, **Ceph**), security frameworks (**RBAC**, **Falco**), and service mesh options (**Istio**, **Linkerd**). Each component requires expertise in configuration, integration, updates, and troubleshooting.

This operational complexity difference - managing a complete platform ecosystem versus consuming managed services - explains why Hetzner typically requires more engineers compared to AWS. The learning curve alone can span months or years, particularly for complex distributed systems like **Ceph** storage clusters.

## Conclusion

The choice between Hetzner Kubernetes and **AWS ECS Fargate** is fundamentally about trade-offs: infrastructure cost versus operational complexity, team size versus expertise requirements, and control versus convenience.

Our analysis reveals three distinct cost zones. Below approximately 700 vCPUs, **AWS ECS Fargate** typically delivers superior TCO due to its minimal operational overhead, allowing lean teams to focus on product development rather than infrastructure management. This makes it ideal for startups, digital agencies, and development environments where time-to-market and team efficiency are paramount.

In the middle zone (700-2,500 vCPUs), the decision becomes more nuanced. Factors beyond pure cost - such as compliance requirements, existing team expertise, and growth predictability - often determine the optimal choice. Companies in this range should carefully evaluate their specific circumstances using the interactive calculator provided in this analysis.

Above 2,000-2,500 vCPUs, Hetzner Kubernetes can deliver substantial cost savings despite requiring larger DevOps teams. However, this advantage only materializes for organizations with strong internal platform capabilities and predictable, high-volume workloads.

For most organizations, especially those prioritizing predictability, scalability, and reduced operational risk, **AWS ECS Fargate** represents the more pragmatic choice. The premium for managed services is often justified by reduced complexity, faster feature delivery, and lower overall risk. Hetzner Kubernetes should primarily be considered by large-scale operations with mature platform engineering capabilities and consistent, high-volume compute requirements where the infrastructure cost differential can offset the substantial operational overhead.

Ultimately, the decision should align with your organization's core competencies: if infrastructure management enhances your competitive advantage, Hetzner may be worth the investment. If it's merely a necessary cost center, AWS Fargate's operational simplicity typically delivers superior business value.
