---
title: K8s on Hetzner vs. AWS Fargate
date: 2025-28-09
tags: ["theoretical physics", "quantum gravity"]
subtitle: Total Cost of Ownership analysis for IT-departments
---

# Introduction

This comparison evaluates self-managed Kubernetes clusters deployed on Hetzner Cloud or dedicated servers against AWS ECS Fargate as a fully managed container platform. The analysis considers the total cost of ownership (TCO) over a three-year period, factoring in infrastructure pricing, staffing needs, operational complexity, and scalability.

For simplicity, the cost calculations include only compute usage and exclude storage, bandwidth, and other components. We assume that fewer employees are needed to operate and maintain a highly managed service compared to a traditional setup, with the least or even no operational effort required for SaaS offerings. The following illustration highlights the different levels of management.

![](/images/managed-levels.png)

---

### Hetzner with Kubernetes

Installing Kubernetes on Hetzner with a production-ready setup involves multiple stages, each of which touches on networking, compute, storage, and cluster lifecycle. The process begins with preparing the environment at Hetzner. You typically start by provisioning a set of dedicated or cloud servers through the **Hetzner Cloud Console** or via the **hcloud** CLI/Terraform provider. These machines need to be distributed in a way that guarantees redundancy across zones or data centers. At least three control plane nodes are required for high availability, and several worker nodes must be defined according to the expected workload.

Once the infrastructure layer is ready, the next step is configuring networking and firewalls. Hetzner requires you to set up private networks for inter-node communication and public IP assignments for ingress. You need to define firewall rules so that the Kubernetes control plane components (**API server**, **etcd**, **kube-scheduler**, **kube-controller-manager**) and worker node services (**kubelet**, **kube-proxy**) can talk securely. At this point, **SSH** access and secure key management should be set up to ensure automation can proceed without manual interruptions.

The installation of Kubernetes itself is usually performed with tools such as **kubeadm**, **kops**, or more modern infrastructure-as-code based solutions like **Cluster API** for Hetzner. With **kubeadm**, you would initialize the control plane on the first master node, configure **etcd** for distributed consensus, and then join the additional masters and workers with generated tokens. At this stage, the cluster has the basic core components running but lacks many of the auxiliary systems that make it usable in production.

To reach a mature state, you must deploy around twenty or more additional components. The first of these is a **Container Network Interface (CNI)** plugin. Hetzner does not provide managed networking, so you must choose solutions like **Calico**, **Cilium**, or **Flannel**, which establish pod networking and enforce network policies. Next comes a DNS service, typically **CoreDNS**, which resolves service names inside the cluster. Metrics collection and observability form the next layer: **Prometheus** for monitoring, **Grafana** for visualization, and **metrics-server** for Kubernetes resource metrics. For logging, a common stack is **Fluent Bit** or **Fluentd** shipping to **Elasticsearch** or **Loki**. A distributed tracing solution such as **Jaeger** can be added if microservices communication analysis is needed.

Ingress is a crucial element in Hetzner since there is no native load balancer. You must either deploy an ingress controller like **NGINX** or **Traefik**, combined with a cloud controller manager for Hetzner that provisions load balancers via the **hcloud API**. For certificate management, **cert-manager** automates **Let's Encrypt** TLS provisioning. Storage is also non-trivial: Hetzner offers block storage volumes, but you need to integrate them with the cluster using the **Hetzner CSI driver**. This allows persistent volumes to be attached dynamically to pods. To secure communication and identities, you would bring in a secrets manager such as **HashiCorp Vault** or **sealed-secrets**, alongside **RBAC** policies to restrict access. Security is further strengthened with tools like **Falco** for runtime security and network policy enforcement through the **CNI** plugin.

Beyond the operational baseline, cluster lifecycle management requires **GitOps** or **CI/CD** integration. **Argo CD** or **Flux** can be deployed to manage application manifests declaratively from **Git**. For backup and disaster recovery, **Velero** can be installed to snapshot persistent volumes and cluster state. To support autoscaling, both the **cluster autoscaler** (integrated with Hetzner's API) and the **horizontal pod autoscaler** must be configured. To provide multi-tenancy or fine-grained resource controls, you set up resource quotas, limit ranges, and namespaces, often accompanied by **Open Policy Agent (OPA) Gatekeeper** for policy enforcement. Finally, to support developer workflow, a service mesh like **Istio** or **Linkerd** can be added, enabling advanced traffic routing and service-to-service encryption.

When all these components are in place, the result is a production-ready Kubernetes environment running entirely on Hetzner infrastructure. The installation involves orchestration of compute provisioning, networking configuration, secure initialization, and deployment of approximately twenty critical supporting systems ranging from networking, monitoring, storage, ingress, and security to lifecycle management and developer tooling. The overall process is iterative: after the initial setup, constant refinement of policies, scaling strategies, and security measures is required to keep the cluster robust and future-proof. 

You will probably need several weeks to become familiar with all the software components, and it could take months or even years to truly master more complex software like Ceph. Overall, this setup presents a significant challenge, even for experienced DevOps engineers.

### AWS ECS Fargate

To set up **ECS Fargate** with Terraform in a simple way, you need only a few building blocks. First, you define an **ECS cluster**, which is essentially a logical grouping where your tasks will run. Then you create a **task definition**. This describes what container image you want to run, how much CPU and memory it should have, and what ports it exposes. You can think of it as a blueprint for a single containerized application.

Once the **task definition** is ready, you define a **service**. A **service** tells **ECS** how many copies of your task to run and keeps them running. With **Fargate**, you don't need to manage servers, so Terraform will just request that **AWS** launches your containers on its serverless compute environment.

For networking, you need a **VPC**, **subnets**, and **security groups**. Terraform can either create these for you or use existing ones. You make sure your **ECS service** is placed in **subnets** with internet access if you want the application to be public. To expose it, you can attach an **Application Load Balancer**, and Terraform will connect the **ECS service** to a **target group** so traffic flows correctly.

So the flow looks like this: define the network (**VPC**, **subnets**, **security groups**), create the **ECS cluster**, write a **task definition** with your container image, and finally create a **service** that runs that task on **Fargate**. Terraform ties this all together in code, so you can apply it and **AWS** provisions everything automatically.

With today's AI-assisted IDEs like **Claude** and **Cursor**, you can assemble a setup like this in Terraform within a few hours. The result will be a robust, automatically updating, and highly managed set of **AWS** components that require minimal maintenance.

---

## Cost structure

| Category                | Hetzner Kubernetes                                    | AWS ECS Fargate                               |
|--------------------------|--------------------------------------------------------|-----------------------------------------------|
| **VM/Compute (monthly)** | 2 vCPU + 4 GB: ~$6<br>4 vCPU + 8 GB: ~$17<br>8 vCPU + 16 GB: ~$33 | 2 vCPU + 4 GB: ~$55<br>4 vCPU + 8 GB: ~$110<br>8 vCPU + 16 GB: ~$210 |
| **Staffing (annual)**    | 5–10 DevOps engineers, ~$550k–1,100k per year          | 1–3 Cloud engineers, ~$110k–330k per year     |
| **3-Year Staffing TCO**  | ~$1.65M–3.3M                                          | ~$330k–990k                                   |

In addition to cloud VMs, Hetzner also offers dedicated servers. These provide significantly more compute at lower per-vCPU cost but require the same level of self-management.  

For example:
- A dedicated server with **16 vCPU and 64 GB RAM** can cost around **$100–120 per month**, whereas equivalent capacity with Hetzner Cloud VMs would be roughly **$260–280 per month**. 

This means dedicated servers can be **50–60% cheaper per vCPU** compared to cloud VMs, but the trade-off is reduced flexibility (no rapid scaling) and the same operational burden of managing Kubernetes, storage, and databases directly.

We assume a baseline of **110k for one DevOps/Cloud Engineer per year**. This number can vary greatly across different countries. It's possible to adjust the given numbers and do a recalculation.

![](/images/tco.png)

The chart above shows the 3-year TCO compared to the average monthly vCPUs from 0 to 5000, with the break-even band highlighted. The lower bound, based on Hetzner in the best case with 5 DevOps versus AWS in the worst case with 3 cloud engineers, is about 733 vCPUs. The upper bound, based on Hetzner in the worst case with 10 DevOps versus AWS in the best case with 1 cloud engineer, is about 3300 vCPUs.

Below roughly 700 to 800 vCPUs on average, AWS ECS Fargate is usually cheaper due to lower staffing needs. Above roughly 3300 vCPUs on average, Hetzner Kubernetes can become cheaper, provided there is strong internal platform capability. Between these points, the outcome depends on the actual staffing mix and utilization profile.

In general, unless you operate very large applications that require massive compute resources or petabytes of monthly data transfer, a highly managed infrastructure tends to be the more cost-effective choice.


---

## Complexity of deployment and operations

### Hetzner Kubernetes
- **Deployment**. Teams must assemble a production-grade Kubernetes cluster from dozens of components. Failures often arise from networking (**Cilium** and kernel compatibility), control plane upgrades (**etcd**), and persistent storage (**Ceph**).  
- **Maintenance**. Kubernetes minor version upgrades, OS patches, **Ceph** balancing, and operator updates must be performed by the DevOps team.  
- **Monitoring**. Requires running **Prometheus**, **Grafana**, **Alertmanager**, and log aggregation systems. On-call responsibilities are higher than in managed solutions.  

### AWS ECS Fargate
- **Deployment**. Services are described declaratively and deployed via **ECS**. No Kubernetes control plane or node OS is managed by the customer.  
- **Maintenance**. AWS handles OS patching, underlying infrastructure scaling, and high availability.  
- **Monitoring**. AWS provides native metrics and logs. Customers can focus on application SLOs instead of platform health.  

---

## Scaling behavior with 10x lower traffic overnight
- **Hetzner Kubernetes**. The cluster autoscaler can scale worker nodes down, but a baseline of nodes is required for the control plane and storage. **Ceph** and **Postgres** clusters prevent scaling to near zero, leaving fixed costs.  
- **AWS ECS Fargate**. Scaling tasks down is straightforward. Overnight workloads can be reduced to a minimal footprint, lowering costs nearly linearly with usage.  

---

## Databases and state
- Hetzner. **Postgres** must be self-managed on VMs or as a Kubernetes operator. High availability, backups, and upgrades require operational investment. **Ceph** clusters add complexity but provide persistence.  
- **AWS ECS Fargate**. Paired with **RDS** or **Aurora** for relational databases. These are fully managed, with SLAs and built-in high availability. Costs are higher, but operational burden is much lower.  

---

## Pain points on Hetzner
- Lack of a first-party CDN.  
- No managed database services.  
- Kernel and **Cilium** compatibility issues during upgrades.
- **Ceph's** operational complexity and risk.
- **etcd** upgrade risks for Kubernetes control plane stability.
- Support limited to infrastructure; Kubernetes troubleshooting is up to the customer.

---

## Conclusion
For mid-sized companies, **ECS Fargate** usually minimizes TCO once staffing is factored in. Hetzner Kubernetes may be attractive if infrastructure cost savings are substantial and the company already has a strong DevOps team. However, the operational risk and manpower overhead are significant.  

**AWS ECS Fargate** is generally more suitable when predictability, scalability, and reduced staffing costs are priorities. Hetzner Kubernetes is only preferable when raw infrastructure savings outweigh the additional DevOps staffing and operational risks over a multi-year horizon.
```
