#!/usr/bin/env python3
"""
网络可达性验证 - 云网络安全的核心 FV 应用

场景：验证微服务架构中，外网是否存在路径直连内网数据库
参考：Azure Network Verification / AWS VPC Reachability Analyzer
"""

from z3 import Solver, Bool, And, Or, Not, sat


def check_network_isolation():
    """检测场景 1：网络隔离性验证"""
    print("=" * 70)
    print("场景 1: 网络隔离性验证")
    print("=" * 70)
    
    s = Solver()
    
    # 网络节点
    internet = Bool('internet')
    dmz = Bool('dmz')
    app_subnet = Bool('app_subnet')
    db_subnet = Bool('db_subnet')
    
    # 防火墙规则
    fw_internet_to_dmz = And(internet, dmz)
    fw_dmz_to_app = And(dmz, app_subnet)
    fw_app_to_db = And(app_subnet, db_subnet)
    
    # 路由传播
    reach_internet_to_dmz = fw_internet_to_dmz
    reach_dmz_to_app = fw_dmz_to_app
    reach_app_to_db = fw_app_to_db
    
    # 间接可达性
    reach_internet_to_app = And(reach_internet_to_dmz, reach_dmz_to_app)
    reach_internet_to_db = And(reach_internet_to_app, reach_app_to_db)
    
    # 检查：外网是否能到达数据库？
    s.add(internet)
    s.add(db_subnet)
    s.add(reach_internet_to_db)
    
    print("\n网络拓扑: [Internet] --> [DMZ] --> [App] --> [DB]")
    print("\n检查：外网是否可以直接或间接访问数据库？")
    
    if s.check() == sat:
        print("\n🚨 发现网络隔离漏洞！")
        print("\n攻击路径:")
        print("  Internet -> DMZ (允许 80/443)")
        print("  DMZ -> App (应用调用)")
        print("  App -> DB (数据库连接)")
        print("\n风险：外网可以通过多层跳转访问内网数据库！")
    else:
        print("\n✅ 网络隔离正确，外网无法访问数据库")


def check_microservice_segmentation():
    """检测场景 2：微服务网络分段验证"""
    print("\n" + "=" * 70)
    print("场景 2: 微服务网络分段验证")
    print("=" * 70)
    
    s = Solver()
    
    # 微服务
    user_service = Bool('user_service')
    payment_service = Bool('payment_service')
    allow_user_payment = Bool('allow_user_payment')
    
    # 检查：User Service 是否可以直接访问 Payment？
    s.add(user_service)
    s.add(payment_service)
    s.add(allow_user_payment)
    
    print("\n检查：User Service 是否可以直接访问 Payment Service？")
    
    if s.check() == sat:
        print("\n🚨 发现微服务分段违规！")
        print("\n风险：User Service 可以直接访问 Payment Service")
        print("  违反最小权限原则，如果 User Service 被攻破...")
    else:
        print("\n✅ 微服务分段正确")


def main():
    print("""
╔══════════════════════════════════════════════════════════════════════╗
║     网络可达性验证器 - 云网络安全 FV 应用                            ║
╚══════════════════════════════════════════════════════════════════════╝
""")
    
    check_network_isolation()
    check_microservice_segmentation()
    
    print("\n" + "=" * 70)
    print("Z3 在网络验证中的核心价值：")
    print("  - 验证安全域之间的隔离策略")
    print("  - 发现间接访问路径")
    print("  - 验证零信任架构")
    print("=" * 70)


if __name__ == "__main__":
    main()
