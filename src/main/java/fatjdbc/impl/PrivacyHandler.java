package fatjdbc.impl;

import org.apache.calcite.avatica.AvaticaConnection;
import org.apache.calcite.avatica.HandlerImpl;

import java.sql.SQLException;

public class PrivacyHandler extends HandlerImpl {
    @Override
    public void onConnectionInit(AvaticaConnection c) throws SQLException {
    }
}