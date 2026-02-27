# 06-Network-Reachability

## 场景描述

**网络可达性验证 - 云网络安全的核心 FV 应用**

参考：Azure Network Watcher / AWS VPC Reachability Analyzer

### 核心问题

几千个防火墙规则、VPC 路由表、安全组叠加后，**人脑无法判断"从 A 到 B 是否可达"**

### 为什么用 Z3

| 特性 | 说明 |
|-----|------|
| 图可达性 | 网络拓扑可以建模为图，用布尔变量表示连通性 |
| 规则组合 | 防火墙规则的组合可以用布尔逻辑表达 |
| 路径搜索 | 求解器可以自动发现间接访问路径 |

### 实际应用

- **AWS VPC Reachability Analyzer**: 验证 VPC 网络配置
- **Azure Network Watcher**: 诊断网络连通性问题
- **Google Cloud Connectivity Tests**: 验证网络路径

## 检测场景

### 场景 1：网络隔离性验证

验证外网是否无法直接访问内网数据库

```
网络拓扑: [Internet] --> [DMZ] --> [App] --> [DB]

检查：外网是否可以直接或间接访问数据库？
```

### 场景 2：微服务网络分段验证

验证微服务之间是否遵循最小权限通信

```
Frontend -> API Gateway -> User/Order/Payment

检查：User Service 是否可以直接访问 Payment Service？
```

## 运行命令

```bash
cd /home/pentester/fv/fv-playground/06-Network-Reachability
python3 network_verification.py
```

## 学习要点

1. **网络建模方法**
   - 节点用布尔变量表示
   - 边用防火墙规则表示
   - 可达性用布尔逻辑传播

2. **实际应用价值**
   - 验证零信任架构
   - 发现网络隔离漏洞
   - 审计安全组配置

3. **扩展方向**
   - 结合云平台 API 自动获取网络配置
   - 集成到 DevSecOps 流程
   - 实时网络监控和告警
