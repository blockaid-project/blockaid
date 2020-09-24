INSERT INTO `data_sources` VALUES (1,'H2','jdbc:h2:mem:DbServerYCSBTest;DB_CLOSE_DELAY=-1',1,0,'CANONICAL','JDBC',NULL,NULL,NULL);
INSERT INTO `jdbc_sources` VALUES (1,'sa','');

update ds_sets set default_datasource_id = 1 where id = 1;
